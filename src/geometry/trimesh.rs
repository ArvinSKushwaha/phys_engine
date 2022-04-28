//! This module contains an implementation of a [`TriMesh`] representing a mesh
//! of triangles. This mesh used use the Face-Vertex data structure to store the
//! associated vertex data for each triangle in a fixed size array of length 3.
//! The [`TriMesh`] can only represent triangles and is therefore more efficient for meshes
//! with only triangles.
//!
//! [`TriMesh`] types can be converted to [`PolyMesh`] types by using the [`TriMesh::into_poly_mesh`]
//! method. This method will construct a new [`PolyMesh`] with the same vertex data as
//! the [`TriMesh`] while converting the triangles of the [`TriMesh`] into faces with
//! 3 vertices.
//!
//! [`PolyMesh`] types can be converted to [`TriMesh`] types by using the [`PolyMesh::into_tri_mesh`]
//! method. This method will construct a new [`TriMesh`] with the same vertex data as
//! the [`PolyMesh`] while triangulating the faces of the [`PolyMesh`] with more than
//! 3 vertices. This method will aim to avoid creating slivers in the resulting
//! mesh.
//!
//! TODO: Add more rigorous tests for [`TriMesh`] methods.
//! FIXME: Ensure documentation is correct.

use crate::errors::PhysEngineErrors;
use ultraviolet::Vec3;

use super::polymesh::PolyMesh;
use super::primitives::{Polygon, Triangle};
use super::utils::get_normal;

/// A struct representing a mesh of triangles. Contains
/// a [`Vec<Triangle>`] of the triangles in the mesh. The [`TriMesh`] also contains
/// a [`Vec<Vec3>`] of the vertices in the mesh. The triangles contain indices
/// into the [`Vec<Vec3>`] of the vertices.
///
/// The triangles comprising the mesh are expected to have the vertices in
/// counter-clockwise order. This is how the normal is calculated. If this
/// is not the case, the normal can be flipped by using the [`TriMesh::flip_normal`]
/// method.
#[derive(Debug, Clone, Default)]
pub struct TriMesh {
    /// The list of triangles in the mesh.
    pub(crate) triangles: Vec<Triangle>,
    /// The list of vertices in the mesh.
    pub(crate) vertices: Vec<Vec3>,
}

impl TriMesh {
    /// Creates empty [`TriMesh`] with no triangles and no vertices.
    ///
    /// # Returns
    /// An empty [`TriMesh`].
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::trimesh::TriMesh;
    /// let mesh = TriMesh::new();
    ///
    /// assert_eq!(mesh.triangles().len(), 0);
    /// assert_eq!(mesh.vertices().len(), 0);
    /// ```
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates a new [`TriMesh`] from a list of vertices and a list of triangles.
    ///
    /// # Arguments
    ///
    /// * `vertices` - A list of vertices.
    /// * `triangles` - A list of triangles.
    ///
    /// # Returns
    /// A new [`Result<TriMesh, PhysEngineErrors>`] containing [`Ok(TriMesh)`] with the given
    /// vertices and triangles or [`Err(PhysEngineErrors::IndicesOutOfBounds)`] if the
    /// indices of the triangles are out of bounds.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::trimesh::TriMesh;
    /// use phys_engine::geometry::primitives::Triangle;
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = vec![
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    /// ];
    ///
    /// let triangles = vec![
    ///   Triangle::new(&[0, 1, 2], &vertices).unwrap(), // Ok(Triangle)
    /// ];
    ///
    /// let mesh = TriMesh::from(&vertices, &triangles).unwrap(); // We know this is valid.
    ///
    /// assert_eq!(mesh.triangles().len(), 1);
    /// assert_eq!(mesh.vertices().len(), 3);
    ///
    /// assert_eq!(mesh.triangles()[0].vertices(), [0, 1, 2]);
    /// assert_eq!(mesh.triangles()[0].normal(), Vec3::new(0.0, 0.0, 1.0));
    /// ```
    pub fn from(vertices: &[Vec3], triangles: &[Triangle]) -> Result<Self, PhysEngineErrors> {
        // Ensure that each triangle's vertex indices are valid. If any are
        // invalid, return an error.
        if triangles
            .iter()
            .any(|t| t.vertices.iter().any(|&v| v >= vertices.len()))
        {
            return Err(PhysEngineErrors::IndicesOutOfBounds);
        }
        Ok(TriMesh {
            vertices: vertices.to_vec(),
            triangles: triangles.to_vec(),
        })
    }

    /// Returns a reference to the list of triangles in the mesh.
    ///
    /// # Returns
    /// A `&[Triangle]` slice containing the triangles in the mesh.
    pub fn triangles(&self) -> &[Triangle] {
        &self.triangles
    }

    /// Returns the a reference to the list of vertices in the mesh.
    ///
    /// # Returns
    /// A `&[Vec3]` slice containing the vertices in the mesh.
    pub fn vertices(&self) -> &[Vec3] {
        &self.vertices
    }

    /// Adds a new triangle to the [`TriMesh`].
    ///
    /// # Arguments
    /// * `vertices` - The three vertices of the triangle as [`Vec3`]s.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::trimesh::TriMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = TriMesh::new();
    /// mesh.add_triangle(
    ///     [
    ///         Vec3::new(0.0, 0.0, 0.0),
    ///         Vec3::new(1.0, 0.0, 0.0),
    ///         Vec3::new(0.0, 1.0, 0.0)
    ///     ],
    /// );
    ///
    /// assert_eq!(mesh.triangles().len(), 1);
    /// assert_eq!(mesh.vertices().len(), 3);
    ///
    /// assert_eq!(mesh.triangles()[0].vertices(), [0, 1, 2]);
    /// assert_eq!(mesh.triangles()[0].normal(), Vec3::new(0.0, 0.0, 1.0));
    /// ```
    ///
    /// This method has the danger of having duplicate vertices in the mesh.
    pub fn add_triangle(&mut self, vertices: [Vec3; 3]) {
        self.triangles.push(Triangle {
            vertices: [
                self.vertices.len(),
                self.vertices.len() + 1,
                self.vertices.len() + 2,
            ],
            normal: get_normal(vertices[0], vertices[1], vertices[2]),
        });
        self.vertices.extend_from_slice(&vertices);
    }

    /// Deduplicates the vertices in the [`TriMesh`]. This method is in-place.
    /// This method is useful for meshes that have many duplicate vertices,
    /// like those using the [`TriMesh::add_triangle`] method. This method
    /// removes all duplicate vertices and replaces them with a single vertex
    /// at the first occurrence of the duplicate. All points with distance less
    /// than `max_dist` are considered duplicates. This method is O(n^2), if a
    /// faster implementation is found please let me know by creating an issue
    /// on GitHub.
    ///
    /// # Arguments
    /// * `max_dist` - The maximum distance between two vertices that will be
    /// considered the same.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::trimesh::TriMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let epsilon = 0.1;
    ///
    /// let mut mesh = TriMesh::new();
    ///
    /// mesh.add_triangle([
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.add_triangle([
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.dedup_vertices(epsilon);
    ///
    /// assert_eq!(mesh.vertices().len(), 3);
    ///
    /// assert_eq!(mesh.triangles()[0].vertices(), &[0, 1, 2]);
    /// assert_eq!(mesh.triangles()[1].vertices(), &[0, 1, 2]);
    /// ```
    pub fn dedup_vertices(&mut self, max_dist: f32) {
        let mut new_vertices = Vec::new();
        let mut new_triangles = Vec::new();

        let compare_vertices = |a: &Vec3, b: &Vec3| (*a - *b).mag_sq() < max_dist * max_dist;

        // Create a map of old vertex indices to their new indices.
        let mut vertex_map = Vec::new();

        // Iterate over all the vertices in the mesh and all vertices in new_vertices.
        // Using [`compare_vertices`] as the comparison function,
        // check if the two vertices are the same. If they are, add the old
        // vertex index to the map and add the new vertex index to the list.
        // Otherwise, map the old vertex index to itself.
        //
        // Note: This is a quadratic algorithm, if any better algorithm is
        // available, it should be implemented here.

        self.vertices.iter().for_each(|v| {
            match new_vertices.iter().position(|nv| compare_vertices(v, nv)) {
                Some(j) => {
                    vertex_map.push(j);
                }
                None => {
                    vertex_map.push(new_vertices.len());
                    new_vertices.push(*v);
                }
            }
        });

        self.triangles.iter().for_each(|t| {
            new_triangles.push(Triangle {
                vertices: [
                    vertex_map[t.vertices[0]],
                    vertex_map[t.vertices[1]],
                    vertex_map[t.vertices[2]],
                ],
                normal: t.normal,
            });
        });

        self.vertices = new_vertices;
        self.triangles = new_triangles;
    }

    /// Remove unused vertices from the [`TriMesh`]. This method is in-place.
    /// This method is useful for meshes that have many hanging vertices. This
    /// method removes all vertices that are not referenced by any triangle.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::trimesh::TriMesh;
    /// use phys_engine::geometry::primitives::Triangle;
    ///
    /// use ultraviolet::Vec3;
    ///
    /// let vertex_list = vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(5.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)
    /// ];
    ///
    /// let mut mesh = TriMesh::from(
    ///     &vertex_list,
    ///     &[Triangle::new(&[0, 2, 3], &vertex_list).unwrap()]
    /// ).unwrap();
    ///
    /// mesh.remove_unused_vertices();
    ///
    /// assert_eq!(mesh.vertices().len(), 3);
    /// assert_eq!(mesh.triangles()[0].vertices(), &[0, 1, 2]);
    /// ```
    pub fn remove_unused_vertices(&mut self) {
        let mut new_vertices = Vec::new();
        let mut new_triangles = Vec::new();

        let mut indices: Vec<_> = self.triangles.iter().flat_map(|t| t.vertices).collect();
        indices.sort();
        indices.dedup();

        indices.iter().for_each(|&i| {
            new_vertices.push(self.vertices[i]);
        });

        self.triangles.iter().for_each(|t| {
            new_triangles.push(
                Triangle::new(
                    &[
                        indices.binary_search(&t.vertices[0]).unwrap(),
                        indices.binary_search(&t.vertices[1]).unwrap(),
                        indices.binary_search(&t.vertices[2]).unwrap(),
                    ],
                    &new_vertices,
                )
                .unwrap(),
            );
        });

        self.vertices = new_vertices;
        self.triangles = new_triangles;
    }

    /// Flips the normal of the triangle at the given index. This method is in-place.
    /// This method is useful for meshes that have been created with indices that
    /// aren't counter-clockwise.
    ///
    /// # Arguments
    /// * `index` - The index of the triangle to flip.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::trimesh::TriMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = TriMesh::new();
    ///
    /// mesh.add_triangle([
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.flip_normal(0);
    ///
    /// assert_eq!(mesh.triangles()[0].normal(), Vec3::new(0.0, 0.0, -1.0));
    /// ```
    pub fn flip_normal(&mut self, index: usize) {
        self.triangles[index].normal = -self.triangles[index].normal;
    }

    /// Converts the [`TriMesh`] to a [`PolyMesh`]. This method will convert the
    /// triangles of the [`TriMesh`] into polygons with 3 vertices.
    ///
    /// # Returns
    /// A [`PolyMesh`] with the same vertices and polygons as the [`TriMesh`].
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::{
    ///     polymesh::PolyMesh,
    ///     trimesh::TriMesh,
    ///     primitives::Triangle
    /// };
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)
    /// ];
    ///
    /// let triangles = vec![
    ///    Triangle::new(&[0, 1, 2], &vertices).unwrap()
    /// ];
    ///
    /// let mut mesh = TriMesh::from(&vertices, &triangles).unwrap(); // Safe to unwrap
    ///
    /// let poly_mesh = mesh.into_poly_mesh();
    /// assert_eq!(poly_mesh.vertices().len(), 3);
    /// assert_eq!(poly_mesh.polygons().len(), 1);
    /// assert_eq!(poly_mesh.polygons()[0].vertices(), &[0, 1, 2]);
    /// ```
    pub fn into_poly_mesh(self) -> PolyMesh {
        let mut polygons = Vec::new();
        for triangle in self.triangles {
            polygons.push(Polygon {
                vertices: vec![
                    triangle.vertices[0],
                    triangle.vertices[1],
                    triangle.vertices[2],
                ],
                normal: triangle.normal,
            });
        }
        PolyMesh {
            vertices: self.vertices,
            polygons,
        }
    }

    /// Returns the SDF (signed distance field) of the [`TriMesh`] at a point. The SDF is
    /// a signed distance function from a point to the mesh.
    ///
    /// The SDF is:
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
    fn sdf(&self, point: Vec3) -> f32 {
        todo!("Implement SDF for TriMesh")
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_tri_mesh_dedup() {
        use super::TriMesh;
        use ultraviolet::Vec3;

        let epsilon = 0.1;

        let mut mesh = TriMesh::new();

        mesh.add_triangle([
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(0.0, 1.0, 0.0),
        ]);

        mesh.add_triangle([
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(0.0, 1.0, 0.0),
        ]);

        mesh.dedup_vertices(epsilon);

        assert_eq!(mesh.vertices().len(), 3);

        assert_eq!(mesh.triangles()[0].vertices(), &[0, 1, 2]);
        assert_eq!(mesh.triangles()[1].vertices(), &[0, 1, 2]);
    }
}
