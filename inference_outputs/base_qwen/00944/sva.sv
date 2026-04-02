module mux4_1_assertions (
    input logic CLK,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic D0, D1, D2, D3, S0, S1,
    output logic Y
);
    // Mux2_1 always block should not drive X to 'x' when S is valid
    mux2_1_no_x: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) $rose(S) |-> (mux2_1.X != 1'bx)
    );

    // Mux4_1 should output the correct value based on S0 and S1
    mux4_1_output_correct: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) (S0 == 1'b0 && S1 == 1'b0) |-> (Y == D0)
    ) else $error("Mux4_1 output is incorrect when S0=0 and S1=0");

    mux4_1_output_correct_1: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) (S0 == 1'b0 && S1 == 1'b1) |-> (Y == D1)
    ) else $error("Mux4_1 output is incorrect when S0=0 and S1=1");

    mux4_1_output_correct_2: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) (S0 == 1'b1 && S1 == 1'b0) |-> (Y == D2)
    ) else $error("Mux4_1 output is incorrect when S0=1 and S1=0");

    mux4_1_output_correct_3: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) (S0 == 1'b1 && S1 == 1'b1) |-> (Y == D3)
    ) else $error("Mux4_1 output is incorrect when S0=1 and S1=1");

    // Mux2_1 should not drive X to 'x' when S is invalid
    mux2_1_no_x_invalid: assert property (
        @(posedge CLK) disable iff (!VPWR || !VGND) (S != 2'b00 && S != 2'b01 && S != 2'b10 && S != 2'b11) |-> (mux2_1.X != 1'bx)
    );

endmodule