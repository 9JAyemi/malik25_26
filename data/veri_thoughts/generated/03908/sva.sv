module FSM_sva #(
    parameter n = 4,
    parameter m = 2,
    parameter s = 8
) (
    input  logic [n-1:0] in,
    input  logic         rst,
    input  logic         clk,
    input  logic [m-1:0] out,
    input  logic [s-1:0] state
);

    localparam [s-1:0] STATE_RESET = 3'b000;
    localparam [s-1:0] STATE_A     = 3'b001;
    localparam [s-1:0] STATE_B     = 3'b010;
    localparam [s-1:0] STATE_C     = 3'b011;
    localparam [s-1:0] STATE_D     = 3'b100;
    localparam [s-1:0] STATE_E     = 3'b101;
    localparam [s-1:0] STATE_F     = 3'b110;
    localparam [s-1:0] STATE_G     = 3'b111;

    localparam [m-1:0] OUT_00 = 2'b00;
    localparam [m-1:0] OUT_01 = 2'b01;
    localparam [m-1:0] OUT_10 = 2'b10;
    localparam [m-1:0] OUT_11 = 2'b11;

    localparam [n-1:0] IN_0000 = 4'b0000;
    localparam [n-1:0] IN_0001 = 4'b0001;
    localparam [n-1:0] IN_0010 = 4'b0010;
    localparam [n-1:0] IN_0011 = 4'b0011;
    localparam [n-1:0] IN_0100 = 4'b0100;
    localparam [n-1:0] IN_0101 = 4'b0101;
    localparam [n-1:0] IN_0110 = 4'b0110;
    localparam [n-1:0] IN_0111 = 4'b0111;
    localparam [n-1:0] IN_1000 = 4'b1000;
    localparam [n-1:0] IN_1001 = 4'b1001;
    localparam [n-1:0] IN_1010 = 4'b1010;

    // A sampled reset forces RESET state and 00 output by the next clock.
    check_reset_forces_reset_state: assert property (
        @(posedge clk) rst |=> (state == STATE_RESET) && (out == OUT_00)
    );

    // RESET and G states drive output 00.
    check_out_for_reset_and_g: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_RESET) || (state == STATE_G)) |-> (out == OUT_00)
    );

    // A and D states drive output 01.
    check_out_for_a_and_d: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_A) || (state == STATE_D)) |-> (out == OUT_01)
    );

    // B and E states drive output 10.
    check_out_for_b_and_e: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_B) || (state == STATE_E)) |-> (out == OUT_10)
    );

    // C and F states drive output 11.
    check_out_for_c_and_f: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_C) || (state == STATE_F)) |-> (out == OUT_11)
    );

    // Any unmapped state drives the default output 00.
    check_out_for_unmapped_state: assert property (
        @(posedge clk) disable iff (rst)
        !((state == STATE_RESET) || (state == STATE_A) || (state == STATE_B) || (state == STATE_C) ||
          (state == STATE_D) || (state == STATE_E) || (state == STATE_F) || (state == STATE_G))
        |-> (out == OUT_00)
    );

    // RESET transitions to A on input 0000.
    check_reset_to_a: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_RESET) && (in == IN_0000)) |=> (state == STATE_A)
    );

    // A transitions to B on input 0001.
    check_a_to_b: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_A) && (in == IN_0001)) |=> (state == STATE_B)
    );

    // A transitions to C on input 0010.
    check_a_to_c: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_A) && (in == IN_0010)) |=> (state == STATE_C)
    );

    // B transitions to D on input 0011.
    check_b_to_d: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_B) && (in == IN_0011)) |=> (state == STATE_D)
    );

    // B or C transitions to E on its matching input.
    check_b_or_c_to_e: assert property (
        @(posedge clk) disable iff (rst)
        (((state == STATE_B) && (in == IN_0100)) ||
         ((state == STATE_C) && (in == IN_0101))) |=> (state == STATE_E)
    );

    // C transitions to F on input 0110.
    check_c_to_f: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_C) && (in == IN_0110)) |=> (state == STATE_F)
    );

    // D, E, and F transition to G on their matching inputs.
    check_d_e_f_to_g: assert property (
        @(posedge clk) disable iff (rst)
        (((state == STATE_D) && (in == IN_0111)) ||
         ((state == STATE_E) && (in == IN_1000)) ||
         ((state == STATE_F) && (in == IN_1001))) |=> (state == STATE_G)
    );

    // G transitions back to RESET on input 1010.
    check_g_to_reset: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_G) && (in == IN_1010)) |=> (state == STATE_RESET)
    );

    // RESET holds when input is not 0000.
    check_reset_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_RESET) && (in != IN_0000)) |=> (state == STATE_RESET)
    );

    // A holds when input is neither 0001 nor 0010.
    check_a_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_A) && (in != IN_0001) && (in != IN_0010)) |=> (state == STATE_A)
    );

    // B holds when input is neither 0011 nor 0100.
    check_b_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_B) && (in != IN_0011) && (in != IN_0100)) |=> (state == STATE_B)
    );

    // C holds when input is neither 0101 nor 0110.
    check_c_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_C) && (in != IN_0101) && (in != IN_0110)) |=> (state == STATE_C)
    );

    // D holds when input is not 0111.
    check_d_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_D) && (in != IN_0111)) |=> (state == STATE_D)
    );

    // E holds when input is not 1000.
    check_e_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_E) && (in != IN_1000)) |=> (state == STATE_E)
    );

    // F holds when input is not 1001.
    check_f_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_F) && (in != IN_1001)) |=> (state == STATE_F)
    );

    // G holds when input is not 1010.
    check_g_holds_without_match: assert property (
        @(posedge clk) disable iff (rst)
        ((state == STATE_G) && (in != IN_1010)) |=> (state == STATE_G)
    );

endmodule