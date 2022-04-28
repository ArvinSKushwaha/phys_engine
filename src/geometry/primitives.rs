//! This module defines two geometric primitives:
//! - [`Triangle`]
//! - [`Polygon`]

use super::utils::{get_normal, is_coplanar};
use crate::errors::PhysEngineErrors;

use ultraviolet::Vec3;

/// A struct representing a [`Triangle`] in 3D space.
/// The [`Triangle`] contains the indices of the three vertices that make up the
/// triangle.
#[derive(Debug, Clone)]
pub struct Triangle {
    /// The three vertices of the triangle.
    /// Note: These vertices must be in counter-clockwise order.
    pub(crate) vertices: [usize; 3],
    /// The normal of the triangle.
    pub(crate) normal: Vec3,
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
    pub(crate) vertices: Vec<usize>,
    /// The normal of the polygon.
    pub(crate) normal: Vec3,
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

    /// Returns a reference to the three vertices of the triangle.
    ///
    /// # Returns
    /// A `&[usize]` slice containing the three vertices of the triangle.
    pub fn vertices(&self) -> &[usize] {
        &self.vertices
    }

    /// Returns the normal of the triangle.
    ///
    /// # Returns
    /// A [`Vec3`] object representing the normal of the triangle.
    pub fn normal(&self) -> Vec3 {
        self.normal
    }
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
    /// use phys_engine::geometry::primitives::Polygon;
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
    /// assert_eq!(polygon.vertices(), vec![0, 1, 2, 3]);
    /// assert_eq!(polygon.normal(), Vec3::new(0.0, 0.0, 1.0));
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

    /// Returns the a reference to the list of vertices that make up the polygon.
    ///
    /// # Returns
    /// A `&[usize]` slice containing the indices of the vertices that make up the polygon.
    pub fn vertices(&self) -> &[usize] {
        &self.vertices
    }

    /// Returns the normal of the polygon.
    ///
    /// # Returns
    /// A [`Vec3`] object representing the normal of the polygon.
    pub fn normal(&self) -> Vec3 {
        self.normal
    }
}
