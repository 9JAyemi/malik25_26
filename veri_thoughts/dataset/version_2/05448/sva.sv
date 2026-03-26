module shift_register_3_bit_sva (
    input logic A,
    input logic load,
    input logic clk,
    input logic Q2,
    input logic Q1,
    input logic Q0
);

    // Q0 samples A on every clock edge.
    check_q0_captures_a: assert property (
        @(posedge clk) 1'b1 |=> (Q0 == $past(A))
    );

    // When load is high, all three bits load the input value.
    check_parallel_load_all_bits: assert property (
        @(posedge clk) load |=> ((Q2 == $past(A)) && (Q1 == $past(A)) && (Q0 == $past(A)))
    );

    // In shift mode, Q2 takes the previous Q1 value.
    check_shift_q2_from_q1: assert property (
        @(posedge clk) !load |=> (Q2 == $past(Q1))
    );

    // In shift mode, Q1 takes the previous Q0 value.
    check_shift_q1_from_q0: assert property (
        @(posedge clk) !load |=> (Q1 == $past(Q0))
    );

endmodule