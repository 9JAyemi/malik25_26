module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] min
);
    // min equals the minimum of a,b,c,d.
    check_min_function: assert property (
        @(posedge a[0]) min == ((a < b) ? ((c < d) ? c : d) : ((c < d) ? c : b))
    );

    // min is less than or equal to each input.
    check_min_le_inputs: assert property (
        @(posedge a[0]) (min <= a) && (min <= b) && (min <= c) && (min <= d)
    );

    // If a is less than all others, min equals a.
    check_select_a_when_min: assert property (
        @(posedge a[0]) ((a < b) && (a < c) && (a < d)) |-> (min == a)
    );

    // If b is less than all others, min equals b.
    check_select_b_when_min: assert property (
        @(posedge a[0]) ((b < a) && (b < c) && (b < d)) |-> (min == b)
    );

    // If c is less than all others, min equals c.
    check_select_c_when_min: assert property (
        @(posedge a[0]) ((c < a) && (c < b) && (c < d)) |-> (min == c)
    );

    // If d is less than all others, min equals d.
    check_select_d_when_min: assert property (
        @(posedge a[0]) ((d < a) && (d < b) && (d < c)) |-> (min == d)
    );

    // If a equals b and is less than c,d, min equals a.
    check_select_a_when_a_eq_b: assert property (
        @(posedge a[0]) ((a == b) && (a < c) && (a < d)) |-> (min == a)
    );

    // If c equals d and is less than a,b, min equals c.
    check_select_c_when_c_eq_d: assert property (
        @(posedge a[0]) ((c == d) && (c < a) && (c < b)) |-> (min == c)
    );

    // If a equals b and c equals d, min equals the smaller of a and c.
    check_select_min_of_pairs: assert property (
        @(posedge a[0]) ((a == b) && (c == d)) |-> (min == ((a < c) ? a : c))
    );

    // If a equals b and c equals d and a equals c, min equals a.
    check_select_a_when_all_equal: assert property (
        @(posedge a[0]) ((a == b) && (c == d) && (a == c)) |-> (min == a)
    );
endmodule