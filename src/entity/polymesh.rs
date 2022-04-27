//! This module contains an implementation of a `PolyMesh` representing a mesh
//! of polygons and `TriMesh` representing a mesh of triangles. Both meshes
//! use the Face-Vertex data structure to store their data. The `PolyMesh`
//! stores the associated vertex data for each face in a `Vec` and the
//! `TriMesh` stores the associated vertex data for each triangle in a fixed
//! size array of length 3.
//!
//! The `PolyMesh` is a more general version of the `TriMesh` and can be used
//! to represent any mesh with any number of vertices per face. The `TriMesh`
//! can only represent triangles and is therefore more efficient for meshes
//! with only triangles.
//!
//! `PolyMesh` types can be converted to `TriMesh` types by using the `into_tri_mesh`
//! method. This method will construct a new `TriMesh` with the same vertex data as
//! the `PolyMesh` while triangulating the faces of the `PolyMesh` with more than
//! 3 vertices. This method will aim to avoid creating slivers in the resulting
//! mesh.
//!
//! `TriMesh` types can be converted to `PolyMesh` types by using the `into_poly_mesh`
//! method. This method will construct a new `PolyMesh` with the same vertex data as
//! the `TriMesh` while converting the triangles of the `TriMesh` into faces with
//! 3 vertices.

use ultraviolet::Vec3;

/// A struct representing a `Triangle` in 3D space.
/// The `Triangle` contains the indices of the three vertices that make up the
/// triangle.
#[derive(Debug, Clone)]
pub struct Triangle {
    /// The three vertices of the triangle.
    /// Note: These vertices must be in counter-clockwise order.
    pub vertices: [usize; 3],
    /// The normal of the triangle.
    pub normal: Vec3,
}

impl Triangle {
    /// Creates a new `Triangle` with the given vertices.
    /// The normal of the triangle will be calculated from the vertices.
    /// The normal will be normalized.
    ///
    /// # Arguments
    /// * `vertices` - The three vertices of the triangle.
    /// * `vertex_list` - The list of vertices that make up the mesh.
    ///
    /// # Returns
    /// A new `Triangle` with the given vertices.
    pub fn new(vertices: [usize; 3], vertex_list: &[Vec3]) -> Triangle {
        let normal = (vertex_list[vertices[1]] - vertex_list[vertices[0]])
            .cross(vertex_list[vertices[2]] - vertex_list[vertices[0]])
            .normalized();
        Triangle { vertices, normal }
    }
}

/// A struct representing a `Polygon` in 3D space.
/// The `Polygon` contains the indices of the vertices that make up the
/// polygon.
#[derive(Debug, Clone)]
pub struct Polygon {
    /// The list of vertices that make up the polygon.
    ///
    /// Note: These vertices must be in counter-clockwise order.
    /// Additionally, the vertices must be coplanar.
    pub vertices: Vec<usize>,
    /// The normal of the polygon.
    pub normal: Vec3,
}

/// A struct representing a mesh of triangles. Contains
/// a `Vec<Triangle>` of the triangles in the mesh. The `TriMesh` also contains
/// a `Vec<Vec3>` of the vertices in the mesh. The triangles contain indices
/// into the `Vec<Vec3>` of the vertices.
#[derive(Debug, Clone)]
pub struct TriMesh {
    /// The list of triangles in the mesh.
    pub triangles: Vec<Triangle>,
    /// The list of vertices in the mesh.
    pub vertices: Vec<Vec3>,
}

/// A struct representing a mesh of polygons. Contains
/// a `Vec<Polygon>` of the polygons in the mesh. The `PolyMesh` also contains
/// a `Vec<Vec3>` of the vertices in the mesh. The polygons contain indices
/// into the `Vec<Vec3>` of the vertices.
#[derive(Debug, Clone)]
pub struct PolyMesh {
    /// The list of polygons in the mesh.
    pub polygons: Vec<Polygon>,
    /// The list of vertices in the mesh.
    pub vertices: Vec<Vec3>,
}

impl TriMesh {
    /// Creates empty `TriMesh` with no triangles and no vertices.
    ///
    /// # Returns
    /// An empty `TriMesh`.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::TriMesh;
    /// let mesh = TriMesh::new();
    ///
    /// assert_eq!(mesh.triangles.len(), 0);
    /// assert_eq!(mesh.vertices.len(), 0);
    /// ```
    pub fn new() -> TriMesh {
        TriMesh {
            triangles: Vec::new(),
            vertices: Vec::new(),
        }
    }

    /// Creates a new `TriMesh` from a list of vertices and a list of triangles.
    ///
    /// # Arguments
    ///
    /// * `vertices` - A list of vertices.
    /// * `triangles` - A list of triangles.
    ///
    /// # Returns
    /// A new `Option<TriMesh>` containing `Some(TriMesh)` with the given
    /// vertices and triangles or `None` if the indices of the triangles are
    /// out of bounds.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::{TriMesh, Triangle};
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = vec![
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    /// ];
    ///
    /// let triangles = vec![
    ///   Triangle { vertices: [0, 1, 2], normal: Vec3::new(0.0, 0.0, 1.0) },
    /// ];
    ///
    /// let mesh = TriMesh::from(vertices, triangles).unwrap(); // We know this is valid.
    ///
    /// assert_eq!(mesh.triangles.len(), 1);
    /// assert_eq!(mesh.vertices.len(), 3);
    ///
    /// assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
    /// assert_eq!(mesh.triangles[0].normal, Vec3::new(0.0, 0.0, 1.0));
    /// ```
    pub fn from(vertices: Vec<Vec3>, triangles: Vec<Triangle>) -> Option<TriMesh> {
        // Ensure that each triangle's vertex indices are valid. If any are
        // invalid, return None.
        if triangles
            .iter()
            .any(|t| t.vertices.iter().any(|&v| v >= vertices.len()))
        {
            return None;
        }
        Some(TriMesh {
            vertices,
            triangles,
        })
    }

    /// Adds a new triangle to the `TriMesh`.
    ///
    /// # Arguments
    ///
    /// * `vertices` - The three vertices of the triangle as `Vec3`s.
    /// * `normal` - The normal of the triangle.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::TriMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = TriMesh::new();
    /// mesh.add_triangle(
    ///     [
    ///         Vec3::new(0.0, 0.0, 0.0),
    ///         Vec3::new(1.0, 0.0, 0.0),
    ///         Vec3::new(0.0, 1.0, 0.0)
    ///     ],
    ///     Vec3::new(0.0, 0.0, 1.0)
    /// );
    ///
    /// assert_eq!(mesh.triangles.len(), 1);
    /// assert_eq!(mesh.vertices.len(), 3);
    ///
    /// assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
    /// assert_eq!(mesh.triangles[0].normal, Vec3::new(0.0, 0.0, 1.0));
    /// ```
    ///
    /// This method has the danger of having duplicate vertices in the mesh.
    pub fn add_triangle(&mut self, vertices: [Vec3; 3], normal: Vec3) {
        self.triangles.push(Triangle {
            vertices: [
                self.vertices.len(),
                self.vertices.len() + 1,
                self.vertices.len() + 2,
            ],
            normal,
        });
        self.vertices.extend_from_slice(&vertices);
    }

    /// Deduplicates the vertices in the `TriMesh`. This method is in-place.
    /// This method is useful for meshes that have many duplicate vertices,
    /// like those using the `TriMesh::add_triangle` method. This method
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
    /// use phys_engine::entity::polymesh::TriMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let epsilon = 0.1;
    ///
    /// let mut mesh = TriMesh::new();
    ///
    /// mesh.add_triangle(
    ///    [
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0)
    ///    ],
    ///    Vec3::new(0.0, 0.0, 1.0)
    /// );
    ///
    /// mesh.add_triangle(
    ///   [
    ///   Vec3::new(0.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 0.0, 0.0),
    ///   Vec3::new(0.0, 1.0, 0.0)
    ///   ],
    ///   Vec3::new(0.0, 0.0, 1.0)
    /// );
    ///
    /// mesh.dedup_vertices(epsilon);
    ///
    /// assert_eq!(mesh.vertices.len(), 3);
    ///
    /// assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
    /// assert_eq!(mesh.triangles[1].vertices, [0, 1, 2]);
    /// ```
    pub fn dedup_vertices(&mut self, max_dist: f32) {
        let mut new_vertices = Vec::new();
        let mut new_triangles = Vec::new();

        let compare_vertices = |a: &Vec3, b: &Vec3| {
            (*a - *b).mag_sq() < max_dist * max_dist
        };

        use std::collections::HashMap;

        // Create a map of old vertex indices to their new indices.
        let mut vertex_map = HashMap::new();

        // Iterate over all the vertices in the mesh and all vertices in new_vertices.
        // Using `compare_vertices` as the comparison function,
        // check if the two vertices are the same. If they are, add the old
        // vertex index to the map and add the new vertex index to the list.
        // Otherwise, map the old vertex index to itself.
        //
        // Note: This is a quadratic algorithm, if any better algorithm is
        // available, it should be implemented here.
        // TODO: Implement a better algorithm.

        self.vertices.iter().enumerate().for_each(|(i, v)| {
            match new_vertices.iter().position(|nv| compare_vertices(v, nv)) {
                Some(j) => {
                    vertex_map.insert(i, j);
                }
                None => {
                    vertex_map.insert(i, new_vertices.len());
                    new_vertices.push(*v);
                }
            }
        });

        self.triangles.iter().for_each(|t| {
            new_triangles.push(Triangle {
                vertices: [
                    vertex_map[&t.vertices[0]],
                    vertex_map[&t.vertices[1]],
                    vertex_map[&t.vertices[2]],
                ],
                normal: t.normal,
            });
        });

        self.vertices = new_vertices;
        self.triangles = new_triangles;
    }

    /// Converts the `TriMesh` to a `PolyMesh`. This method will convert the
    /// triangles of the `TriMesh` into polygons with 3 vertices.
    ///
    /// # Returns
    /// A `PolyMesh` with the same vertices and polygons as the `TriMesh`.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::{PolyMesh, TriMesh, Triangle};
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = TriMesh::new();
    /// mesh.vertices.extend(vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)]
    /// );
    /// mesh.triangles.extend(vec![Triangle {
    ///    vertices: [0, 1, 2],
    ///    normal: Vec3::new(0.0, 0.0, 1.0)
    /// }]);
    ///
    /// let poly_mesh = mesh.into_poly_mesh();
    /// assert_eq!(poly_mesh.vertices.len(), 3);
    /// assert_eq!(poly_mesh.polygons.len(), 1);
    /// assert_eq!(poly_mesh.polygons[0].vertices, vec![0, 1, 2]);
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
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_tri_mesh_dedup() {
        use super::TriMesh;
        use ultraviolet::Vec3;

        let epsilon = 0.1;

        let mut mesh = TriMesh::new();

        mesh.add_triangle(
           [
           Vec3::new(0.0, 0.0, 0.0),
           Vec3::new(1.0, 0.0, 0.0),
           Vec3::new(0.0, 1.0, 0.0)
           ],
           Vec3::new(0.0, 0.0, 1.0)
        );

        mesh.add_triangle(
          [
          Vec3::new(0.0, 0.0, 0.0),
          Vec3::new(1.0, 0.0, 0.0),
          Vec3::new(0.0, 1.0, 0.0)
          ],
          Vec3::new(0.0, 0.0, 1.0)
        );

        mesh.dedup_vertices(epsilon);

        assert_eq!(mesh.vertices.len(), 3);

        assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
        assert_eq!(mesh.triangles[1].vertices, [0, 1, 2]);
    }
}
