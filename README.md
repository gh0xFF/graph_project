# Graph reader application with own graph library with std only deps

## The project consists of two parts

- a library that provides basic methods for working with graphs and serialization/deserialization files in .tgf format.
- a utility for parsing and printing the graph.

# The project contains a makefile to simplify project assembly (works only in *nix)

To build the release version

```make
make build
```

To launch the release version

```make
make run
```

After building the project in ```/target/coverage```, you can view the test coverage, and the ```/doc``` directory with documentation for the library also appears

# Usage examples

Print graph from file

```rust
    Graph::<String>::deserialize_from_tgf("graph.tgf").unwrap();
    
    for vertex in &graph.vertices {
        println!("{}", vertex.id);

        for edge in graph.edges.iter().filter(|e| e.start == vertex.id) {
            println!("{}", edge.end);
        }
    }
```

Basic methods examples with graph object

```rust
    use graph_project::Graph;

    let mut graph: Graph<i32> = Graph::new();
    graph.add_vertex(1, 10);
    graph.add_vertex(2, 20);
    graph.add_edge(1, 2, 1);

    graph.breadth_first_traversal(1);

    graph.remove_edge(1, 2);
    graph.remove_vertex(1);
    graph.remove_vertex(2);
```

To see more examples see tests in ```/src/lib.rs```