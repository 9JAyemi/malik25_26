module sky130_fd_sc_hd__nor4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

// Y must equal the 4-input NOR of A, B, C, and D.
    check_nor_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

// When all inputs are low, Y must be high.
    check_all_low_drives_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

// A high must force Y low.
    check_a_high_drives_low: assert property (
        @(posedge clk) A |-> !Y
    );

// B high must force Y low.
    check_b_high_drives_low: assert property (
        @(posedge clk) B |-> !Y
    );

// C high must force Y low.
    check_c_high_drives_low: assert property (
        @(posedge clk) C |-> !Y
    );

// D high must force Y low.
    check_d_high_drives_low: assert property (
        @(posedge clk) D |-> !Y
    );

// A high Y implies all inputs are low.
    check_high_output_requires_all_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

// A low Y implies at least one input is high.
    check_low_output_requires_some_high: assert property (
        @(posedge clk) !Y |-> (A || B || C || D)
    );

endmodule
