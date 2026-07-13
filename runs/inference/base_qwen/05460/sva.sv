module shift_register_sva (
    input logic data_in,
    input logic shift_clk,
    input logic reset,
    output logic [3:0] q0,
    output logic [3:0] q1,
    output logic [3:0] q2,
    output logic [3:0] q3
);
    // Reset behavior: All outputs should be 0 when reset is active
    reset_behavior: assert property (
        @(posedge shift_clk) disable iff (!reset) (reset |-> (q0 == 4'b0000) && (q1 == 4'b0000) && (q2 == 4'b0000) && (q3 == 4'b0000))
    );

    // Shift behavior: Each output should shift to the next on the rising edge of shift_clk
    shift_behavior: assert property (
        @(posedge shift_clk) disable iff (!reset) (q0 == data_in) && (q1 == q0) && (q2 == q1) && (q3 == q2)
    );
endmodule