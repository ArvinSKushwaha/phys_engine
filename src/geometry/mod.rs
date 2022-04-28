//! This module contains an implementation of a [`PolyMesh`] representing a mesh
//! of polygons and [`TriMesh`] representing a mesh of triangles. Both meshes
//! use the Face-Vertex data structure to store their data. The [`PolyMesh`]
//! stores the associated vertex data for each face in a [`Vec`] and the
//! [`TriMesh`] stores the associated vertex data for each triangle in a fixed
//! size array of length 3.
//!
//! See the [`PolyMesh`] and [`TriMesh`] documentation for more information.
//!
//! This module also contains a [`Collider`] enum that represents a collection
//! of collider shapes, among which are [`Collider::Sphere`], [`Collider::AABB`],
//! [`Collider::Cuboid`], and [`Collider::Mesh`].
//!
//! See the [`Collider`] documentation for more information.
//!
//! This module contains an implementation of a [`Ray`] and [`Intersection`]
//! structs that represent a ray and the intersection between a ray and a collider.
//!
//! See the [`Ray`] and [`Intersection`] documentation for more information.

pub mod collision;
pub mod polymesh;
pub mod primitives;
pub mod ray;
pub mod trimesh;
pub mod utils;

pub use self::collision::Collider;
pub use self::polymesh::PolyMesh;
pub use self::primitives::{Polygon, Triangle};
pub use self::ray::{Intersection, Ray};
pub use self::trimesh::TriMesh;
