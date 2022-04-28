//! This module defines the [`Mesh`] trait, which is used to represent general geometries.
//! [`Mesh`] gives implementors the ability to define collision detection and ray intersection,
//! both of which are necessary for physics simulations and rendering.

use ultraviolet::Vec3;

use super::ray::{Ray, Intersection};


/// A trait for defining a general mesh. Meshes are used to represent collision detection and
/// ray intersection.
///
/// # Methods
/// * `is_colliding` - Returns whether or not the mesh is colliding with another arbitrary mesh.
/// * `get_intersection_point` - Returns the point of intersection between the mesh and a ray.
pub trait Mesh {
    /// Returns whether the two geometries are colliding. The implementation
    /// expectes that for `a: &dyn Geometry` and `b: &dyn Geometry`, `a.is_colliding(b)`
    /// is equivalent to `b.is_colliding(a)`.
    ///
    /// # Arguments
    /// * `other` - The other geometry to check for collision.
    ///
    /// # Returns
    /// `true` if the two geometries are colliding, `false` otherwise.
    fn is_colliding(&self, other: &dyn Mesh) -> bool;

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
    fn get_intersection_point(&self, ray: Ray, t_min: f32) -> Option<Intersection>;

    /// Returns the SDF (signed distance field) of the mesh at a point. The SDF is a signed distance
    /// function from a point to the mesh. The SDF is:
    /// * `< 0` if the point is inside the mesh.
    /// * `= 0` if the point is on the mesh.
    /// * `> 0` if the point is outside the mesh.
    ///
    /// The SDF is used to determine whether or not a point is inside a mesh.
    ///
    /// # Arguments
    /// * `point` - The point to check the SDF at.
    ///
    /// # Returns
    /// The SDF at the point.
    fn sdf(&self, point: Vec3) -> f32;
}
