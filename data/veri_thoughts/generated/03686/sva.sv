module lookahead_assertions (
    input logic clk,
    input logic c_in,
    input logic c_out,
    input logic [2:0] c,
    input logic [3:0] p,
    input logic [3:0] g,
    input logic P,
    input logic G
);

    // c[0] matches the bit-0 carry lookahead equation.
    check_c0_equation: assert property (
        @(posedge clk)
        c[0] == (g[0] | (p[0] & c_in))
    );

    // c[1] matches the bit-1 carry lookahead equation.
    check_c1_equation: assert property (
        @(posedge clk)
        c[1] == (g[1] | (g[0] & p[1]) | (p[1] & p[0] & c_in))
    );

    // c[2] matches the bit-2 carry lookahead equation.
    check_c2_equation: assert property (
        @(posedge clk)
        c[2] == (g[2] | (g[1] & p[2]) | (g[0] & p[1] & p[2]) | (p[2] & p[1] & p[0] & c_in))
    );

    // c_out matches the final carry lookahead equation.
    check_cout_equation: assert property (
        @(posedge clk)
        c_out == (g[3] | (g[2] & p[3]) | (g[1] & p[2] & p[3]) |
                  (g[0] & p[1] & p[2] & p[3]) | (p[3] & p[2] & p[1] & p[0] & c_in))
    );

    // G matches the group-generate equation.
    check_group_generate_equation: assert property (
        @(posedge clk)
        G == (g[3] | (g[2] & p[3]) | (g[1] & p[2] & p[3]) | (p[3] & p[2] & p[1] & g[0]))
    );

    // P matches the group-propagate equation.
    check_group_propagate_equation: assert property (
        @(posedge clk)
        P == (p[3] & p[2] & p[1] & p[0])
    );

    // c[1] is the recursive carry form using c[0].
    check_c1_recursive_form: assert property (
        @(posedge clk)
        c[1] == (g[1] | (p[1] & c[0]))
    );

    // c[2] is the recursive carry form using c[1].
    check_c2_recursive_form: assert property (
        @(posedge clk)
        c[2] == (g[2] | (p[2] & c[1]))
    );

    // c_out is the recursive carry form using c[2].
    check_cout_recursive_form: assert property (
        @(posedge clk)
        c_out == (g[3] | (p[3] & c[2]))
    );

    // c_out must equal group generate OR propagated c_in.
    check_cout_group_relation: assert property (
        @(posedge clk)
        c_out == (G | (P & c_in))
    );

endmodule