//! This module contains an implementation of a [`PolyMesh`] representing a mesh
//! of polygons and [`TriMesh`] representing a mesh of triangles. Both meshes
//! use the Face-Vertex data structure to store their data. The [`PolyMesh`]
//! stores the associated vertex data for each face in a [`Vec`] and the
//! [`TriMesh`] stores the associated vertex data for each triangle in a fixed
//! size array of length 3.
//!
//! The [`PolyMesh`] is a more general version of the [`TriMesh`] and can be used
//! to represent any mesh with any number of vertices per face. The [`TriMesh`]
//! can only represent triangles and is therefore more efficient for meshes
//! with only triangles.
//!
//! [`PolyMesh`] types can be converted to [`TriMesh`] types by using the [`PolyMesh::into_tri_mesh`]
//! method. This method will construct a new [`TriMesh`] with the same vertex data as
//! the [`PolyMesh`] while triangulating the faces of the [`PolyMesh`] with more than
//! 3 vertices. This method will aim to avoid creating slivers in the resulting
//! mesh.
//!
//! [`TriMesh`] types can be converted to [`PolyMesh`] types by using the [`TriMesh::into_poly_mesh`]
//! method. This method will construct a new [`PolyMesh`] with the same vertex data as
//! the [`TriMesh`] while converting the triangles of the [`TriMesh`] into faces with
//! 3 vertices.
//!
//! TODO: Add more rigorous tests for the [`PolyMesh`] and [`TriMesh`] methods.
//! FIXME: Ensure documentation is correct.

use crate::errors::PhysEngineErrors;
use ultraviolet::Vec3;

/// Computes the normal vector to 3 vertices in counter-clockwise order.
///
/// # Arguments
/// * [`v0`] - The first vertex of the triangle.
/// * [`v1`] - The second vertex of the triangle.
/// * [`v2`] - The third vertex of the triangle.
///
/// # Returns
/// A [`Vec3`] object representing the normal vector to the vertices. This function
/// uses the right-hand rule.
///
pub(crate) fn get_normal(v0: Vec3, v1: Vec3, v2: Vec3) -> Vec3 {
    let v1 = v1 - v0;
    let v2 = v2 - v0;
    v1.cross(v2)
}

/// Checks if vertices are coplanar. This is done by checking that each cross product
/// points in the same direction.
///
/// # Arguments
/// * [`vertices`] - A slice of [`Vec3`] points to check for coplanarity.
///
/// # Returns
/// [`true`] if the vertices are coplanar, otherwise [`false`].
pub(crate) fn is_coplanar(vertices: &[Vec3]) -> bool {
    const COPLANARITY_TOLERANCE: f32 = 0.00001;
    // Naive Algorithm, simply check that all cross products are collinear.
    // Should be O(n) which is fast, but also, makes me sad.
    let normal = get_normal(vertices[0], vertices[1], vertices[2]);
    for window in vertices.windows(3) {
        let normal2 = get_normal(window[0], window[1], window[2]);
        if normal2.cross(normal).mag_sq() > COPLANARITY_TOLERANCE {
            return false;
        }
    }
    true
}

/// A struct representing a [`Triangle`] in 3D space.
/// The [`Triangle`] contains the indices of the three vertices that make up the
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
    /// Creates a new [`Triangle`] with the given vertices.
    /// The normal of the triangle will be calculated from the vertices.
    /// The normal will be normalized.
    ///
    /// # Arguments
    /// * `vertices` - The three vertices of the triangle.
    /// * `vertex_list` - The list of vertices that make up the mesh.
    ///
    /// # Returns
    /// A new [`Triangle`] with the given vertices.
    pub fn new(vertices: &[usize], vertex_list: &[Vec3]) -> Result<Triangle, PhysEngineErrors> {
        if vertices.len() != 3 {
            return Err(PhysEngineErrors::InvalidInputSize);
        }
        let vertices = [vertices[0], vertices[1], vertices[2]];
        let normal = get_normal(
            vertex_list[vertices[0]],
            vertex_list[vertices[1]],
            vertex_list[vertices[2]],
        );
        Ok(Triangle { vertices, normal })
    }
}

/// A struct representing a [`Polygon`] in 3D space.
/// The [`Polygon`] contains the indices of the vertices that make up the
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

impl Polygon {
    /// Creates a new [`Polygon`] with the given vertices.
    /// The normal of the polygon will be calculated from the vertices.
    /// The normal will be normalized. If the vertices are not coplanar,
    /// no polygon will be created. A polygon also must have at least 3
    /// vertices.
    ///
    /// # Arguments
    /// * `vertices` - The list of vertices that make up the polygon.
    /// * `vertex_list` - The list of vertices that make up the mesh.
    ///
    /// # Returns
    /// An [`Result<Polygon, PhysEngineErrors>`] containing [`Ok(Polygon)`] if the following
    /// conditions are met:
    /// * There are at least 3 vertices. Otherwise,
    /// [`Err(PhysEngineErrors::PolygonInvalidVertexCount)`] is returned.
    /// * The vertices are coplanar. Otherwise, [`Err(PhysEngineErrors::NotCoplanar)`] is returned.
    /// * Indices exist for all vertices in the list. Otherwise,
    /// [`Err(PhysEngineErrors::IndicesOutOfBounds)`] is returned.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::Polygon;
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = vec![
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0),
    /// ];
    ///
    /// let polygon = Polygon::new(&[0, 1, 2, 3], &vertices).unwrap(); // Ok(Polygon)
    ///
    /// assert_eq!(polygon.vertices, vec![0, 1, 2, 3]);
    /// assert_eq!(polygon.normal, Vec3::new(0.0, 0.0, 1.0));
    /// ```
    pub fn new(vertices: &[usize], vertex_list: &[Vec3]) -> Result<Polygon, PhysEngineErrors> {
        let normal = (vertex_list[vertices[1]] - vertex_list[vertices[0]])
            .cross(vertex_list[vertices[2]] - vertex_list[vertices[0]])
            .normalized();

        if vertices.len() < 3 {
            return Err(PhysEngineErrors::PolygonInvalidVertexCount);
        }

        if !is_coplanar(&vertices.iter().map(|&i| vertex_list[i]).collect::<Vec<_>>()) {
            return Err(PhysEngineErrors::NotCoplanar);
        }

        Ok(Polygon {
            vertices: vertices.to_vec(),
            normal,
        })
    }
}

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
    pub triangles: Vec<Triangle>,
    /// The list of vertices in the mesh.
    pub vertices: Vec<Vec3>,
}

/// A struct representing a mesh of polygons. Contains
/// a [`Vec<Polygon>`] of the polygons in the mesh. The [`PolyMesh`] also contains
/// a [`Vec<Vec3>`] of the vertices in the mesh. The polygons contain indices
/// into the [`Vec<Vec3>`] of the vertices.
///
/// The polygons must follow the following rules:
/// * The vertices must be coplanar.
/// * There must be at least 3 vertices.
///
/// It is recommended that the polygons are convex. This is not enforced. If
/// polygon is convex, the normal will be calculated from the vertices by
/// assuming the vertices are in counter-clockwise order and applying the
/// right-hand rule. If not convex, the normal will be guessed from the first
/// three vertices. These normals can be incorrect, but flippable using the
/// [`PolyMesh::flip_normal`] method.
#[derive(Debug, Clone, Default)]
pub struct PolyMesh {
    /// The list of polygons in the mesh.
    pub polygons: Vec<Polygon>,
    /// The list of vertices in the mesh.
    pub vertices: Vec<Vec3>,
}

impl TriMesh {
    /// Creates empty [`TriMesh`] with no triangles and no vertices.
    ///
    /// # Returns
    /// An empty [`TriMesh`].
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::TriMesh;
    /// let mesh = TriMesh::new();
    ///
    /// assert_eq!(mesh.triangles.len(), 0);
    /// assert_eq!(mesh.vertices.len(), 0);
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
    /// let mesh = TriMesh::from(&vertices, &triangles).unwrap(); // We know this is valid.
    ///
    /// assert_eq!(mesh.triangles.len(), 1);
    /// assert_eq!(mesh.vertices.len(), 3);
    ///
    /// assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
    /// assert_eq!(mesh.triangles[0].normal, Vec3::new(0.0, 0.0, 1.0));
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

    /// Adds a new triangle to the [`TriMesh`].
    ///
    /// # Arguments
    ///
    /// * `vertices` - The three vertices of the triangle as [`Vec3`]s.
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
    /// use phys_engine::entity::polymesh::TriMesh;
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
    /// assert_eq!(mesh.vertices.len(), 3);
    ///
    /// assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
    /// assert_eq!(mesh.triangles[1].vertices, [0, 1, 2]);
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
    /// use phys_engine::entity::polymesh::{TriMesh, Triangle};
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
    /// assert_eq!(mesh.vertices.len(), 3);
    /// assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
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
    /// use phys_engine::entity::polymesh::TriMesh;
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
    /// assert_eq!(mesh.triangles[0].normal, Vec3::new(0.0, 0.0, -1.0));
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

impl From<TriMesh> for PolyMesh {
    /// Converts a [`TriMesh`] into a [`PolyMesh`]. This method will convert the
    /// triangles of the [`TriMesh`] into polygons with 3 vertices.
    ///
    /// See [`TriMesh::into_poly_mesh`] for more information.
    fn from(mesh: TriMesh) -> Self {
        mesh.into_poly_mesh()
    }
}

impl PolyMesh {
    /// Creates empty [`PolyMesh`] with no vertices or polygons.
    ///
    /// # Returns
    /// An empty [`PolyMesh`].
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mesh = PolyMesh::new();
    ///
    /// assert_eq!(mesh.vertices.len(), 0);
    /// assert_eq!(mesh.polygons.len(), 0);
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a [`PolyMesh`] from a list of vertices and a list of polygons.
    ///
    /// # Arguments
    /// * `vertices` - A list of vertices.
    /// * `polygons` - A list of polygons.
    ///
    /// # Returns
    /// An [`Result<PolyMesh, PhysEngineErrors>`] containing [`Ok(PolyMesh)`] if the vertices and
    /// polygons are valid, [`Err(PhysEngineErrors)`] otherwise. The vertices and polygons are
    /// valid if:
    /// * Polygons do not contain any vertex that is not in the
    /// vertices list. Otherwise, a [`PhysEngineErrors::IndicesOutOfBounds`] error is returned.
    /// * Polygons are coplanar. Otherwise, a [`PhysEngineErrors::NotCoplanar`] error is returned.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::{PolyMesh, Polygon};
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = [
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0)
    /// ];
    /// let polygons = vec![
    ///   Polygon::new(&[0, 1, 2, 3], &vertices).unwrap()
    /// ];
    ///
    /// let mesh = PolyMesh::from(&vertices, &polygons).unwrap();
    ///
    /// assert_eq!(mesh.vertices.len(), 4);
    /// assert_eq!(mesh.polygons.len(), 1);
    /// assert_eq!(mesh.polygons[0].vertices, vec![0, 1, 2, 3]);
    /// ```
    pub fn from(vertices: &[Vec3], polygons: &[Polygon]) -> Result<Self, PhysEngineErrors> {
        if polygons
            .iter()
            .flat_map(|f| &f.vertices)
            .any(|&f| f >= vertices.len())
        {
            return Err(PhysEngineErrors::IndicesOutOfBounds);
        }
        for polygon in polygons {
            if !is_coplanar(
                &polygon
                    .vertices
                    .iter()
                    .map(|&f| vertices[f])
                    .collect::<Vec<_>>(),
            ) {
                return Err(PhysEngineErrors::NotCoplanar);
            }
            if polygon.vertices.len() < 3 {
                return Err(PhysEngineErrors::PolygonInvalidVertexCount);
            }
        }
        Ok(Self {
            vertices: vertices.to_vec(),
            polygons: polygons.to_vec(),
        })
    }

    /// Adds a new polygon to the [`TriMesh`].
    ///
    /// # Arguments
    /// * `vertices` - A slice of vertices that make up the polygon as [`Vec3`]s.
    ///
    /// # Note
    /// This method has the danger of having duplicate vertices in the mesh.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = PolyMesh::new();
    ///
    /// mesh.add_polygon(&vec![
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// assert_eq!(mesh.vertices.len(), 4);
    /// assert_eq!(mesh.polygons.len(), 1);
    ///
    /// assert_eq!(mesh.polygons[0].vertices, vec![0, 1, 2, 3]);
    /// assert_eq!(mesh.polygons[0].normal, Vec3::new(0.0, 0.0, 1.0));
    /// ```
    ///
    pub fn add_polygon(&mut self, vertices: &[Vec3]) -> Result<(), PhysEngineErrors> {
        if vertices.len() < 3 {
            return Err(PhysEngineErrors::PolygonInvalidVertexCount);
        }

        if !is_coplanar(vertices) {
            return Err(PhysEngineErrors::NotCoplanar);
        }

        self.polygons.push(Polygon {
            vertices: (self.vertices.len()..self.vertices.len() + vertices.len()).collect(),
            normal: get_normal(vertices[0], vertices[1], vertices[2]),
        });
        self.vertices.extend(vertices);
        Ok(())
    }

    /// Deduplicate vertices in the [`PolyMesh`]. This method is useful when you have a
    /// [`PolyMesh`] that has duplicate vertices. This method will remove all duplicate vertices
    /// and replace them with a single vertex. For more information, see the
    /// [`TriMesh::dedup_vertices`] method.
    ///
    /// # Notes
    /// Unlike [`TriMesh::dedup_vertices`], this method does not have a `max_dist` parameter.
    /// This is because the vertices in a [`PolyMesh`] are guaranteed to be coplanar, and even
    /// small vertex displacements can cause the polygons to be non-coplanar.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = PolyMesh::new();
    /// mesh.add_polygon(&vec![
    ///   Vec3::new(0.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 1.0, 0.0),
    ///   Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.add_polygon(&vec![
    ///   Vec3::new(0.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 1.0, 0.0),
    ///   Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.dedup_vertices();
    ///
    /// assert_eq!(mesh.vertices.len(), 4);
    /// assert_eq!(mesh.polygons.len(), 2);
    /// assert_eq!(mesh.polygons[0].vertices, vec![0, 1, 2, 3]);
    /// assert_eq!(mesh.polygons[1].vertices, vec![0, 1, 2, 3]);
    /// ```
    pub fn dedup_vertices(&mut self) {
        let mut new_vertices = Vec::new();
        let mut new_polygons = Vec::new();

        let mut vertex_map = Vec::new();

        self.vertices.iter().for_each(|v| {
            match new_vertices.iter().position(|nv| v == nv) {
                Some(i) => vertex_map.push(i),
                None => {
                    new_vertices.push(*v);
                    vertex_map.push(new_vertices.len() - 1);
                }
            }
        });

        self.polygons.iter().for_each(|p| {
            new_polygons.push(Polygon {
                vertices: p
                    .vertices
                    .iter()
                    .map(|i| vertex_map[*i])
                    .collect(),
                normal: p.normal,
            });
        });

        self.vertices = new_vertices;
        self.polygons = new_polygons;
    }

    /// Remove unused vertices from the [`PolyMesh`]. This method is in-place.
    /// This method is useful for meshes that have many hanging vertices. This
    /// method removes all vertices that are not referenced by any polygon. For
    /// more information, see the [`TriMesh::remove_unused_vertices`] method.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::{PolyMesh, Polygon};
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 1.0, 0.0),
    ///     Vec3::new(0.0, 0.0, 1.0),
    ///     Vec3::new(0.0, 1.0, 0.0),
    /// ];
    ///
    /// let polygons = vec![
    ///    Polygon::new(&[0, 1, 2, 4], &vertices).unwrap(), // Safe to unwrap
    /// ];
    ///
    /// let mut mesh = PolyMesh::from(&vertices, &polygons).unwrap(); // Safe to unwrap
    ///
    /// assert_eq!(mesh.vertices.len(), 5);
    /// assert_eq!(mesh.polygons.len(), 1);
    /// assert_eq!(mesh.polygons[0].vertices, vec![0, 1, 2, 4]);
    ///
    /// mesh.remove_unused_vertices();
    ///
    /// assert_eq!(mesh.vertices.len(), 4);
    /// assert_eq!(mesh.polygons.len(), 1);
    /// assert_eq!(mesh.polygons[0].vertices, vec![0, 1, 2, 3]);
    /// ```
    pub fn remove_unused_vertices(&mut self) {
        let mut new_vertices = Vec::new();
        let mut new_polygons = Vec::new();

        let mut indices: Vec<_> = self.polygons.iter().flat_map(|p| &p.vertices).collect();
        indices.sort();
        indices.dedup();

        indices.iter().for_each(|&&i| {
            new_vertices.push(self.vertices[i]);
        });

        self.polygons.iter().for_each(|p| {
            new_polygons.push(
                Polygon::new(
                    &p.vertices.iter().map(|i| indices.binary_search(&i).unwrap()).collect::<Vec<usize>>(),
                    &new_vertices,
                ).unwrap(),
            );
        });

        self.vertices = new_vertices;
        self.polygons = new_polygons;
    }

    /// Flip the normal of the polygon at the given index. This method is in-place.
    /// This method is useful for meshes containing concave polygons, as they may have
    /// flipped normals.
    ///
    /// # Arguments
    /// * `index` - The index of the polygon to flip.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::entity::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = PolyMesh::new();
    ///
    /// mesh.add_polygon(&vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 1.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.flip_normal(0);
    ///
    /// assert_eq!(mesh.polygons[0].normal, Vec3::new(0.0, 0.0, -1.0));
    /// ```
    pub fn flip_normal(&mut self, index: usize) {
        self.polygons[index].normal = -self.polygons[index].normal;
    }

    /// Make a [`TriMesh`] from the [`PolyMesh`].
    /// FIXME: This method is not implemented yet.
    pub fn into_tri_mesh(&self) -> TriMesh {
        todo!("PolyMesh::into_tri_mesh");
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

        assert_eq!(mesh.vertices.len(), 3);

        assert_eq!(mesh.triangles[0].vertices, [0, 1, 2]);
        assert_eq!(mesh.triangles[1].vertices, [0, 1, 2]);
    }

    #[test]
    fn test_get_normals() {
        use super::get_normal;
        use ultraviolet::Vec3;

        let v0 = Vec3::new(0.0, 0.0, 0.0);
        let v1 = Vec3::new(1.0, 0.0, 0.0);
        let v2 = Vec3::new(0.0, 1.0, 0.0);
        let normal = get_normal(v0, v1, v2);

        assert_eq!(normal, Vec3::new(0.0, 0.0, 1.0));
    }

    #[test]
    fn test_is_coplanar() {
        use super::is_coplanar;
        use ultraviolet::Vec3;

        let vertices = vec![
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(1.0, 1.0, 0.0),
            Vec3::new(0.0, 1.0, 0.0),
        ];

        assert!(is_coplanar(&vertices));
    }
}
