use std::collections::{HashSet, VecDeque};
use std::error::Error;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::rc::Rc;
use std::str::FromStr;

/// Represents a vertex in the graph.
#[derive(Debug, Clone)]
pub struct Vertex<T> {
    /// Unique identifier for the vertex.
    pub id: usize,
    /// Value associated with the vertex.
    pub value: T,
}

/// Represents an edge between two vertices in the graph.
#[derive(Debug, Clone)]
pub struct Edge<T> {
    /// ID of the start vertex of the edge.
    pub start: usize,
    /// ID of the end vertex of the edge.
    pub end: usize,
    /// Value associated with the edge.
    pub value: T,
}

/// Represents a graph data structure.
#[derive(Debug)]
pub struct Graph<T> {
    /// Collection of vertices in the graph.
    pub vertices: Vec<Rc<Vertex<T>>>,
    /// Collection of edges in the graph.
    pub edges: Vec<Edge<T>>,
}

impl<T> Graph<T> {

    /// Creates a new instance of the graph.
    /// # Examples
    /// 
    /// ```
    /// use graph_project::Graph;
    /// 
    /// let graph: Graph<i32> = Graph::new();
    /// assert_eq!(graph.vertices.len(), 0);
    /// assert_eq!(graph.edges.len(), 0);
    /// ```
    pub fn new() -> Self {
        Graph {
            vertices: Vec::new(),
            edges: Vec::new(),
        }
    }

    /// Adds a new vertex to the graph.
    /// # Examples
    /// 
    /// ```
    /// use graph_project::Graph;
    /// 
    /// let mut graph: Graph<String> = Graph::new();
    /// assert_eq!(graph.vertices.len(), 0);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.add_vertex(1, "vertex1".to_string());
    /// assert_eq!(graph.vertices.len(), 1);
    /// assert_eq!(graph.edges.len(), 0);
    /// ```
    pub fn add_vertex(&mut self, id: usize, value: T) {
        self.vertices.push(Vertex { id, value }.into());
    }

    /// Performs a breadth-first traversal starting from the specified vertex.
    /// # Examples
    /// 
    /// ```
    /// use graph_project::Graph;
    /// 
    /// let mut graph: Graph<String> = Graph::new();
    /// graph.add_vertex(1, "1".to_string());
    /// let vertexes = graph.breadth_first_traversal(1);
    /// assert_eq!(vertexes.len(), 1);
    /// ```
    pub fn breadth_first_traversal(&self, start: usize) -> Vec<&Vertex<T>> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut visited_vertices = Vec::new();

        queue.push_back(start);

        while let Some(vertex_id) = queue.pop_front() {
            if !visited.contains(&vertex_id) {
                visited.insert(vertex_id.clone());
                if let Some(vertex) = self.vertices.iter().find(|v| v.id == vertex_id) {
                    visited_vertices.push(vertex.as_ref());
                    for edge in &self.edges {
                        if edge.start == vertex_id {
                            queue.push_back(edge.end);
                        } else if edge.end == vertex_id {
                            queue.push_back(edge.start);
                        }
                    }
                }
            }
        }

        visited_vertices
    }

    /// Removes a vertex and all incident edges from the graph.
    /// # Examples
    /// 
    /// ```
    /// use graph_project::Graph;
    /// 
    /// let mut graph: Graph<String> = Graph::new();
    /// assert_eq!(graph.vertices.len(), 0);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.add_vertex(1, "vertex1".to_string());
    /// assert_eq!(graph.vertices.len(), 1);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.remove_vertex(1);
    /// assert_eq!(graph.vertices.len(), 0);
    /// assert_eq!(graph.edges.len(), 0);
    /// ```
    pub fn remove_vertex(&mut self, id: usize) {
        self.vertices.retain(|v| v.id != id);
        self.edges.retain(|e| e.start != id && e.end != id);
    }

    /// Adds a new edge between two vertices.
    /// # Examples
    /// 
    /// ```
    /// use graph_project::Graph;
    /// 
    /// let mut graph: Graph<i32> = Graph::new();
    /// assert_eq!(graph.vertices.len(), 0);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.add_vertex(1, 1);
    /// graph.add_vertex(2, 2);
    /// 
    /// assert_eq!(graph.vertices.len(), 2);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.add_edge(1, 2, 12);
    /// assert_eq!(graph.vertices.len(), 2);
    /// assert_eq!(graph.edges.len(), 1);
    /// ```
    pub fn add_edge(&mut self, start: usize, end: usize, value: T) {
        self.edges.push(Edge {start: start.into(), end: end.into(), value});
    }

    /// Removes an edge between two vertices.
    /// # Examples
    /// 
    /// ```
    /// use graph_project::Graph;
    /// 
    /// let mut graph: Graph<i32> = Graph::new();
    /// assert_eq!(graph.vertices.len(), 0);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.add_vertex(1, 1);
    /// graph.add_vertex(2, 2);
    /// 
    /// assert_eq!(graph.vertices.len(), 2);
    /// assert_eq!(graph.edges.len(), 0);
    /// 
    /// graph.add_edge(1, 2, 12);
    /// assert_eq!(graph.vertices.len(), 2);
    /// assert_eq!(graph.edges.len(), 1);
    /// 
    /// graph.remove_edge(1, 2);
    /// assert_eq!(graph.vertices.len(), 2);
    /// assert_eq!(graph.edges.len(), 0);
    /// ```
    pub fn remove_edge(&mut self, start: usize, end: usize) {
        self.edges.retain(|e| !(e.start == start && e.end == end));
    }

    /// Serializes the graph to a file in the TGF format.
    /// # Example
    /// 
    /// ```no_run
    /// use graph_project::Graph;
    /// let mut graph: Graph<i32> = Graph::new();
    /// graph.serialize_to_tgf("test_out.tgf", |v| v.to_string()).unwrap();
    /// ```
    pub fn serialize_to_tgf<F>(&self, filename: &str, format_value: F) -> Result<(), Box<dyn Error>>
    where
        F: Fn(&T) -> String,
    {
        let mut file = File::create(filename)?;
        for vertex in &self.vertices {
            writeln!(&mut file, "{} {}", vertex.id, format_value(&vertex.value))?;
        }
        writeln!(&mut file, "#")?;
        for edge in &self.edges {
            writeln!(&mut file, "{} {} {}", edge.start, edge.end, format_value(&edge.value))?;
        }
        Ok(())
    }

    /// Deserializes the graph from a file in the TGF format.
    /// # Example
    /// 
    /// ```no_run
    /// use graph_project::Graph;
    /// 
    /// Graph::<String>::deserialize_from_tgf("test_graph.tgf").unwrap();
    /// ```
    pub fn deserialize_from_tgf<S>(filename: S) -> Result<Graph<T>, Box<dyn Error>>
    where
        T: FromStr + for<'a> std::convert::From<&'a str>,
        T::Err: Error + 'static,
        S: AsRef<str>,
    {
        let file = File::open(filename.as_ref())?;
        let reader = io::BufReader::new(file);

        let (vertices, edges) = Self::parse_tgf::<T, _>(reader)?;

        Ok(Graph { vertices, edges })
    }

    /// Parses the TGF format from a reader.
    /// # Example
    /// 
    /// ```no_run
    /// use graph_project::Graph;
    /// use std::io::BufReader;
    /// use std::fs::File;
    /// 
    /// let file = File::open("graph.tgf").unwrap();
    /// let reader = BufReader::new(file);
    ///
    /// let (vertices, edges) = Graph::<String>::parse_tgf::<String, _>(reader).unwrap();
    /// ```
    pub fn parse_tgf<U, R>(reader: R) -> Result<(Vec<Rc<Vertex<U>>>, Vec<Edge<U>>), Box<dyn Error>>
    where
        U: FromStr + for<'a> std::convert::From<&'a str>,
        U::Err: Error + 'static,
        R: BufRead,
    {
        let mut vertices = Vec::new();
        let mut edges = Vec::new();
        let mut reading_edges = false;

        for line in reader.lines() {
            let line = line?;
            if line == "#" {
                reading_edges = true;
                continue;
            }
            if !reading_edges {
                let mut parts = line.splitn(2, ' ');
                if let (Some(id), Some(value)) = (parts.next(), parts.next()) {
                    vertices.push(Rc::new(Vertex {id: id.parse()?, value: value.into()}));
                } else {
                    return Err(format!("Invalid vertex format: '{}'", line).into());
                }
            } else {
                let mut parts = line.splitn(3, ' ');
                if let (Some(start), Some(end), Some(value)) = (parts.next(), parts.next(), parts.next()) {
                    edges.push(Edge {start: start.parse()?, end: end.parse()?, value: value.parse()?});
                } else {
                    return Err(format!("Invalid edge format: '{}'", line).into());
                }
            }
        }

        Ok((vertices, edges))
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, io::Read};

    use super::*;

    #[test]
    fn test_add_vertex_i32() {
        let mut graph: Graph<i32> = Graph::new();
        assert_eq!(graph.vertices.len(), 0);

        graph.add_vertex(1, 10);
        assert_eq!(graph.vertices.len(), 1);
        assert_eq!(graph.vertices[0].id, 1);
        assert_eq!(graph.vertices[0].value, 10);

        graph.add_vertex(2, 20);
        assert_eq!(graph.vertices.len(), 2);
        assert_eq!(graph.vertices[1].id, 2);
        assert_eq!(graph.vertices[1].value, 20);
    }

    #[test]
    fn test_add_vertex_string() {
        let mut graph: Graph<String> = Graph::new();
        assert_eq!(graph.vertices.len(), 0);

        graph.add_vertex(1, 10.to_string());
        assert_eq!(graph.vertices.len(), 1);
        assert_eq!(graph.vertices[0].id, 1);
        assert_eq!(graph.vertices[0].value, 10.to_string());

        graph.add_vertex(2, 20.to_string());
        assert_eq!(graph.vertices.len(), 2);
        assert_eq!(graph.vertices[1].id, 2);
        assert_eq!(graph.vertices[1].value, 20.to_string());
    }

    #[test]
    fn test_remove_vertex() {
        let mut graph: Graph<i32> = Graph::new();
        assert_eq!(graph.vertices.len(), 0);

        graph.add_vertex(1, 10);
        assert_eq!(graph.vertices.len(), 1);

        graph.add_vertex(2, 20);
        assert_eq!(graph.vertices.len(), 2);

        graph.remove_vertex(1);
        assert_eq!(graph.vertices.len(), 1);

        graph.remove_vertex(2);
        assert_eq!(graph.vertices.len(), 0);
    }

    #[test]
    fn test_add_edge() {
        let mut graph: Graph<i32> = Graph::new();
        graph.add_vertex(1, 10);
        graph.add_vertex(2, 20);
        graph.add_edge(1, 2, 1);
        assert_eq!(graph.edges.len(), 1);
        assert_eq!(graph.edges[0].start, 1);
        assert_eq!(graph.edges[0].end, 2);

        graph.add_vertex(3, 30);
        graph.add_edge(2, 3, 3);
        assert_eq!(graph.edges.len(), 2);
        assert_eq!(graph.edges[1].start, 2);
        assert_eq!(graph.edges[1].end, 3);
    }

    #[test]
    fn test_remove_edge() {
        let mut graph: Graph<i32> = Graph::new();
        graph.add_vertex(1, 10);
        graph.add_vertex(2, 20);
        graph.add_edge(1, 2, 11);
        assert_eq!(graph.edges.len(), 1);
        assert_eq!(graph.edges[0].start, 1);
        assert_eq!(graph.edges[0].end, 2);

        graph.add_vertex(3, 30);
        graph.add_edge(2, 3, 22);
        assert_eq!(graph.edges.len(), 2);
        assert_eq!(graph.edges[1].start, 2);
        assert_eq!(graph.edges[1].end, 3);

        graph.remove_edge(1, 2);
        assert_eq!(graph.edges.len(), 1);

        graph.remove_edge(2, 3);
        assert_eq!(graph.edges.len(), 0);
    }

    #[test]
    fn test_deserialize_from_tgf() {
        let content = r#"1 111
2 222
#
1 2 1212"#;

        let mut file = File::create("test_graph.tgf").unwrap();
        writeln!(&mut file, "{}", content).unwrap();

        match Graph::<String>::deserialize_from_tgf("test_graph.tgf") {
            Ok(graph) => {
                assert_eq!(graph.vertices.len(), 2);
                assert_eq!(graph.edges.len(), 1);
                assert_eq!(graph.vertices[0].id, 1);
                assert_eq!(graph.vertices[1].id, 2);
                assert_eq!(graph.edges[0].start, 1);
                assert_eq!(graph.edges[0].end, 2);
            }
            Err(err) => {
                fs::remove_file("test_graph.tgf").unwrap();
                panic!("Failed to deserialize graph: {:?}", err);
            }
        }
        fs::remove_file("test_graph.tgf").unwrap();
    }

    #[test]
    fn test_serialize_to_tgf() {
        let mut graph: Graph<i32> = Graph::new();
        assert_eq!(graph.vertices.len(), 0);

        graph.add_vertex(1, 111);
        assert_eq!(graph.vertices.len(), 1);

        graph.add_vertex(2, 222);
        assert_eq!(graph.vertices.len(), 2);

        graph.add_edge(1, 2, 1212);
        assert_eq!(graph.edges.len(), 1);

        graph.serialize_to_tgf("test_out.tgf", |v| v.to_string()).unwrap();

        let expected_content = r#"1 111
2 222
#
1 2 1212
"#;

        let mut actual_data = String::with_capacity(20);
        File::open("test_out.tgf")
            .unwrap()
            .read_to_string(&mut actual_data)
            .unwrap();

        assert_eq!(expected_content.len(), actual_data.len());
        assert_eq!(expected_content, actual_data);

        fs::remove_file("test_out.tgf").unwrap();
    }

    #[test]
    fn test_breadth_first_traversal() {
        let mut graph: Graph<i32> = Graph::new();
        graph.add_vertex(1, 10);
        graph.add_vertex(2, 20);
        graph.add_vertex(3, 30);
        graph.add_vertex(4, 40);

        graph.add_edge(1, 2, 5);
        graph.add_edge(1, 3, 15);
        graph.add_edge(2, 4, 25);
        graph.add_edge(3, 4, 35);

        let visited_vertices = graph.breadth_first_traversal(1);

        let mut expected_visited_vertices = vec![1, 2, 3, 4];
        expected_visited_vertices.sort();
        let mut visited_vertices = visited_vertices
            .into_iter()
            .map(|v| v.id)
            .collect::<Vec<_>>();
        visited_vertices.sort();
        assert_eq!(expected_visited_vertices, visited_vertices);
    }
}
