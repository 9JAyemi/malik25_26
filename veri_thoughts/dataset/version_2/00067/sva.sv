module sky130_fd_sc_hd__mux_2_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic S,
    input logic [3:0] Y
);

    // Y must equal A when S is low.
    check_select_a: assert property (
        @(posedge clk) (!S) |-> (Y == A)
    );

    // Y must equal B when S is high.
    check_select_b: assert property (
        @(posedge clk) S |-> (Y == B)
    );

    // Y must always match the mux select equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == (S ? B : A)
    );

    // If A and B are equal, Y must match that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A == B) |-> (Y == A)
    );

endmodule