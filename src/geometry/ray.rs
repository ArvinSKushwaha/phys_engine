//! This module defines the [`Ray`] and [`Intersection`] structs. As named,
//! `Ray` is a ray in 3D space, and `Intersection` is a point of intersection
//! between a ray and an object.

use ultraviolet::Vec3;

/// A ray in 3D space. Stores the origin and direction of the ray.
pub struct Ray {
    /// The origin of the ray.
    pub origin: Vec3,
    /// The direction of the ray.
    pub direction: Vec3,
}

/// A point of intersection between a ray and an object. Stores the point of
/// intersection, the normal at the point of intersection, and the distance
/// from the ray's origin to the point of intersection.
pub struct Intersection {
    /// The distance from the ray's origin to the point of intersection.
    pub distance: f64,
    /// The point of intersection.
    pub point: Vec3,
    /// The normal at the point of intersection.
    pub normal: Vec3,
}
