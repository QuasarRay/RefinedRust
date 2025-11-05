// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Get trait requirements of objects.

use log::{info, trace};
use radium::specs;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use topological_sort::TopologicalSort;

use crate::environment::Environment;
use crate::{search, traits};

/// Determine the origin of a trait obligation.
/// `surrounding_reqs` are the requirements of a surrounding impl or decl.
#[expect(clippy::ref_option)]
fn determine_origin_of_trait_requirement<'tcx>(
    did: DefId,
    tcx: ty::TyCtxt<'tcx>,
    surrounding_reqs: &[ty::TraitRef<'tcx>],
    req: ty::TraitRef<'tcx>,
) -> specs::TyParamOrigin {
    let in_trait_decl = tcx.trait_of_assoc(did);

    if surrounding_reqs.contains(&req) {
        if in_trait_decl.is_some() {
            return specs::TyParamOrigin::SurroundingTrait;
        }
        return specs::TyParamOrigin::SurroundingImpl;
    }
    specs::TyParamOrigin::Direct
}

/// Meta information of a trait requirement.
#[derive(Debug)]
pub(crate) struct TraitReqMeta<'tcx> {
    pub trait_ref: ty::TraitRef<'tcx>,
    pub bound_regions: Vec<ty::BoundRegionKind>,
    pub binders: ty::Binder<'tcx, ()>,
    pub origin: specs::TyParamOrigin,
    /// this requirement is a reflexive trait requirement on `Self` in a trait declaration
    pub is_used_in_self_trait: bool,
    /// this requirement comes from a trait obligation on an associated type
    pub from_obligation: bool,
    /// for the ordered associated types, an optional constraint
    pub assoc_constraints: Vec<Option<ty::Ty<'tcx>>>,
}

/// Internal meta information of a trait requirement.
#[derive(Clone, Debug)]
struct TraitReqProto<'tcx> {
    trait_ref: ty::TraitRef<'tcx>,
    bound_regions: Vec<ty::BoundRegionKind>,
    binders: ty::Binder<'tcx, ()>,
    is_used_in_self_trait: bool,
    from_obligation: bool,
    assoc_constraints: Vec<Option<ty::Ty<'tcx>>>,
}

/// Get the trait requirements of a [did], also determining their origin relative to the [did].
/// The requirements are sorted in a way that is stable across compilations.
pub(crate) fn get_trait_requirements_with_origin<'tcx>(
    env: &Environment<'tcx>,
    did: DefId,
) -> Result<Vec<TraitReqMeta<'tcx>>, super::Error<'tcx>> {
    trace!("Enter get_trait_requirements_with_origin for did={did:?}");
    let typing_env: ty::TypingEnv<'tcx> = ty::TypingEnv::post_analysis(env.tcx(), did);

    // Are we declaring the scope of a trait?
    let is_trait = env.tcx().is_trait(did);

    // Determine whether we are declaring the scope of a trait method or trait impl method
    let in_trait_decl = env.tcx().trait_of_assoc(did);
    let in_trait_impl = env.trait_impl_of_method(did);

    // if this has a surrounding scope, get the requirements declared on that, so that we can
    // determine the origin of this requirement below
    let surrounding_reqs = if let Some(trait_did) = in_trait_decl {
        let trait_param_env = env.tcx().param_env(trait_did);
        get_nontrivial(env, trait_did, trait_param_env, None)?
            .into_iter()
            .map(|x| x.trait_ref)
            .collect()
    } else if let Some(impl_did) = in_trait_impl {
        let impl_param_env = env.tcx().param_env(impl_did);
        get_nontrivial(env, impl_did, impl_param_env, None)?
            .into_iter()
            .map(|x| x.trait_ref)
            .collect()
    } else {
        vec![]
    };

    let clauses = typing_env.param_env.caller_bounds();
    info!("Caller bounds: {:?}", clauses);

    let in_trait_decl = if is_trait { Some(did) } else { in_trait_decl };
    let requirements = get_nontrivial(env, did, typing_env.param_env, in_trait_decl)?;
    let mut annotated_requirements = Vec::new();

    for req in requirements {
        // TODO: we skip these requirements for now
        if req.from_obligation {
            continue;
        }

        let origin = determine_origin_of_trait_requirement(did, env.tcx(), &surrounding_reqs, req.trait_ref);
        info!("Determined origin of requirement {:?} as {origin:?}", req.trait_ref);

        let req = TraitReqMeta {
            trait_ref: req.trait_ref,
            bound_regions: req.bound_regions,
            binders: req.binders,
            from_obligation: req.from_obligation,
            origin,
            is_used_in_self_trait: req.is_used_in_self_trait,
            assoc_constraints: req.assoc_constraints,
        };
        annotated_requirements.push(req);
    }

    trace!(
        "Leave get_trait_requirements_with_origin for did={did:?} with annotated_requirements={annotated_requirements:?}"
    );
    Ok(annotated_requirements)
}

/// `is_used_in_self_trait` recursively marks whether this requirement came from the `Self`
/// requirement of a trait decl, ensuring that also all the obligations get marked accordingly.
fn trait_requirements_of_clauses<'tcx>(
    env: &Environment<'tcx>,
    clauses: ty::Clauses<'tcx>,
    in_trait_decl: Option<DefId>,
    is_used_in_self_trait: bool,
    in_obligation: bool,
    max_recursion_depth: u32,
    out: &mut Vec<TraitReqProto<'tcx>>,
) -> Result<(), super::Error<'tcx>> {
    trace!("enter trait_requirements_of_clauses: clauses = {clauses:?}, in_trait_decl = {in_trait_decl:?}, is_used_in_self_trait = {is_used_in_self_trait:?}, in_obligation = {in_obligation:?}");
    for cl in clauses {
        // only look for trait predicates for now
        let Some(trait_clause) = cl.as_trait_clause() else {
            continue;
        };

        let mut bound_regions = Vec::new();
        let bound_vars = trait_clause.bound_vars();
        for v in bound_vars {
            match v {
                ty::BoundVariableKind::Region(r) => {
                    bound_regions.push(r);
                },
                _ => {
                    unimplemented!("do not support higher-ranked bounds for non-lifetimes");
                },
            }
        }

        // keep the binders around
        let binders = trait_clause.rebind(());
        let trait_pred = trait_clause.skip_binder();

        // We ignore negative polarities for now
        if trait_pred.polarity != ty::PredicatePolarity::Positive {
            continue;
        }

        let trait_ref = trait_pred.trait_ref;

        // filter Sized, Copy, Send, Sync?
        if Some(true) == is_builtin_trait(env.tcx(), trait_ref.def_id) {
            continue;
        }

        // gather constraints on associated types from projection clauses
        // Important in case of recursion: this happens withe the obligation clauses, not the outer clauses.
        let assoc_constraints = traits::get_trait_assoc_constraints(env, clauses, trait_ref);

        // check if we are in the process of translating a trait decl
        let is_self = trait_ref.args[0].as_type().unwrap().is_param(0);
        let is_used_in_self_trait = if let Some(trait_decl_did) = in_trait_decl && trait_decl_did == trait_ref.def_id && is_self {
            // This is the self assumption of the trait we are currently declaring
            // For a function spec in a trait decl, we remember this, as we do not require
            // a quantified spec for the Self trait.
            true
        } else {
            is_used_in_self_trait
        };

        // this is a nontrivial requirement
        let req = TraitReqProto {
            trait_ref, bound_regions, binders, 
            is_used_in_self_trait,
            from_obligation: in_obligation,
            assoc_constraints
        };
        out.push(req);

        // look at associated types and their obligations
        let items: &ty::AssocItems = env.tcx().associated_items(trait_ref.def_id);
        for it in items.in_definition_order() {
            if let ty::AssocKind::Type { .. } = it.kind {
                let it_bounds: ty::EarlyBinder<'tcx, ty::Clauses<'tcx>> = env.tcx().item_bounds(it.def_id);

                trace!("trait_requirements_of_clauses: bounds of assoc {:?} : {it_bounds:?}", it.def_id);

                let bounds = it_bounds.skip_binder();

                // recursively process these bounds
                if max_recursion_depth > 0 {
                    trait_requirements_of_clauses(env, bounds, in_trait_decl, is_used_in_self_trait, true, max_recursion_depth - 1, out)?;
                }
                else {
                    return Err(super::Error::ExceededAssocRecursionDepth(it.def_id));
                }
            }
        }
    }
    trace!("leave trait_requirements_of_clauses");
    Ok(())
}

/// Get non-trivial trait requirements of a `ParamEnv`,
/// ordered deterministically.
fn get_nontrivial<'tcx>(
    env: &Environment<'tcx>,
    for_did: DefId,
    param_env: ty::ParamEnv<'tcx>,
    in_trait_decl: Option<DefId>,
) -> Result<Vec<TraitReqProto<'tcx>>, super::Error<'tcx>> {
    let mut trait_refs = Vec::new();
    trace!(
        "Enter get_nontrivial_trait_requirements with for_did={for_did:?}, param_env = {param_env:?}, in_trait_decl = {in_trait_decl:?}"
    );

    let clauses = param_env.caller_bounds();
    // TODO: hardcoded constant...
    trait_requirements_of_clauses(env, clauses, in_trait_decl, false, false, 100, &mut trait_refs)?;

    // Make sure the order is stable across compilations
    trace!("get_nontrivial_trait_requirements: ordering requirements of {for_did:?}");

    // first sort by dependencies using topological sort
    let mut topo: TopologicalSort<usize> = TopologicalSort::new();

    for (idx, a) in trait_refs.iter().enumerate() {
        topo.insert(idx);
        let mut deps = Vec::new();
        let trait_did = a.trait_ref.def_id;
        trait_get_deps(env, trait_did, &mut deps)?;
        trace!("get_nontrivial_trait_requirements: deps of {trait_did:?}: {deps:?}");
        for did in deps {
            for (idxb, b) in trait_refs.iter().enumerate() {
                if b.trait_ref.def_id == did {
                    topo.add_dependency(idxb, idx);
                }
            }
        }
    }

    let mut defn_order = Vec::new();
    while !topo.is_empty() {
        let next = topo.pop_all();

        let mut next_refs = Vec::new();
        for x in next {
            next_refs.push(trait_refs[x].clone());
        }

        next_refs.sort_by(|a, b| traits::cmp_trait_ref(env, in_trait_decl, &a.trait_ref, &b.trait_ref));

        defn_order.append(&mut next_refs);
    }

    trace!("Leave get_nontrivial_trait_requirements with for_did={for_did:?}, trait_refs = {defn_order:?}");

    Ok(defn_order)
}

fn trait_get_deps<'tcx>(env: &Environment<'tcx>, of_trait: DefId, out: &mut Vec<DefId>) -> Result<(), super::Error<'tcx>> {
    let param_env = env.tcx().param_env(of_trait);
    let clauses = param_env.caller_bounds();
    for cl in clauses {
        // only look for trait predicates for now
        let Some(pred) = cl.as_trait_clause() else {
            continue;
        };
        let trait_pred = pred.skip_binder();

        // We ignore negative polarities for now
        if trait_pred.polarity == ty::PredicatePolarity::Positive {
            let trait_ref = trait_pred.trait_ref;
            if trait_ref.def_id != of_trait {
                out.push(trait_ref.def_id);
            }
        }
    }
    Ok(())
}

/// Check if this is a built-in trait
fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = search::try_resolve_did(tcx, &["core", "marker", "Sized"])?;
    let meta_sized_did = search::try_resolve_did(tcx, &["core", "marker", "MetaSized"])?;
    //let pointee_sized_did = search::try_resolve_did(tcx, &["core", "marker", "PointeeSized"])?;

    // used for closures
    let tuple_did = search::try_resolve_did(tcx, &["core", "marker", "Tuple"])?;

    // Used for const. I suppose for us const is irrelevant, and this feature is extremely
    // underdocumented, so just ignore it.
    let destruct_did = search::try_resolve_did(tcx, &["core", "marker", "Destruct"])?;

    Some(
        trait_did == sized_did
            || trait_did == tuple_did
            || trait_did == meta_sized_did
            || trait_did == destruct_did,
    )
}
