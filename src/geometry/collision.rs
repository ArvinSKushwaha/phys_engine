//! This module defines the [`Collider`] enum, which contains all the different types of colliders.
//! [`Collider`] provides a way to check if two colliders are colliding.
//!
//! These are the different types of colliders:
//! - [`Collider::Sphere`]
//! - [`Collider::AABB`]
//! - [`Collider::Cuboid`]
//! - [`Collider::Mesh`]

use std::rc::Weak;

use ultraviolet::{Rotor3, Vec3};

use super::ray::{Intersection, Ray};
use super::trimesh::TriMesh;

/// An enum containing all the different types of colliders.
/// List of collider types:
pub enum Collider {
    /// A spherical collider; stores the center and radius.
    Sphere { center: Vec3, radius: f32 },

    /// An axis-aligned bounding box; stores the center and half-extents.
    AABB { center: Vec3, half_extents: Vec3 },

    /// A box collider; stores the center, half-extents, and rotation (as a [`Rotor3`]).
    Cuboid {
        center: Vec3,
        half_extents: Vec3,
        orientation: Rotor3,
    },

    /// A mesh collider; stores a weak reference to a [`TriMesh`] ([`Weak<TriMesh>`]).
    Mesh { mesh: Weak<TriMesh> },
}

impl Collider {
    /// Returns whether the two geometries are colliding. The implementation
    /// expectes that for `a: &Collider` and `b: &Collider`, `a.is_colliding(b)`
    /// is equivalent to `b.is_colliding(a)`.
    ///
    /// # Arguments
    /// * `other` - The other [`&Collider`] to check for collision.
    ///
    /// # Returns
    /// `true` if the two geometries are colliding, `false` otherwise.
    pub fn is_colliding(&self, other: &Collider) -> bool {
        todo!("Implement is_colliding for all collider types");
    }

    /// Returns the point of intersection between the mesh and a ray. If the ray does not intersect
    /// the mesh, then `None` is returned, otherwise the point of intersection is returned. The
    /// intersection is represented by [`Intersection`]. The function also takes a `t_min`, which
    /// is the minimum distance from the ray origin to the intersection point that is allowed.
    ///
    /// # Arguments
    /// * `ray` - The ray to check for intersection.
    /// * `t_min` - The minimum distance along the ray to check for intersection.
    ///
    /// # Returns
    /// `Some(Intersection)` if the ray intersects the mesh, `None` otherwise.
    pub fn get_intersection_point(&self, ray: Ray, t_min: f32) -> Option<Intersection> {
        todo!("Implement get_intersection_point");
    }
}
