module control_module_sva (
    input logic [3:0] input_1,
    input logic [1:0] input_2,
    input logic       input_3,
    input logic       input_4,
    input logic       input_5,
    input logic       input_6,
    input logic       input_7,
    input logic       input_8,
    input logic       output_1
);
    // No clock/reset in RTL; sample on posedges of all inputs.

    // When input_1 is 0, output_1 is forced to 0.
    check_sel0_forces_zero: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd0) |-> ##0 (output_1 == 1'b0)
    );

    // When input_1 is 1, output_1 equals input_3.
    check_sel1_routes_input3: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd1) |-> ##0 (output_1 == input_3)
    );

    // When input_1 is 2, output_1 equals input_4.
    check_sel2_routes_input4: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd2) |-> ##0 (output_1 == input_4)
    );

    // When input_1 is 3, output_1 equals input_5.
    check_sel3_routes_input5: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd3) |-> ##0 (output_1 == input_5)
    );

    // When input_1 is 4, output_1 equals input_6.
    check_sel4_routes_input6: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd4) |-> ##0 (output_1 == input_6)
    );

    // When input_1 is 5, output_1 equals input_7.
    check_sel5_routes_input7: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd5) |-> ##0 (output_1 == input_7)
    );

    // When input_1 is 6, output_1 equals input_8.
    check_sel6_routes_input8: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd6) |-> ##0 (output_1 == input_8)
    );

    // When input_1 is 7, output_1 equals input_2[0] (LSB of input_2).
    check_sel7_routes_input2_lsb: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd7) |-> ##0 (output_1 == input_2[0])
    );

    // For input_1 values 8..15 (MSB=1), output_1 is 0 (default case).
    check_default_high_msb_forces_zero: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1[3] == 1'b1) |-> ##0 (output_1 == 1'b0)
    );

    // When selecting 7, changes on input_2[1] do not affect output_1.
    check_sel7_input2_msb_ignored: assert property (
        @(posedge input_1[0] or posedge input_1[1] or posedge input_1[2] or posedge input_1[3]
          or posedge input_2[0] or posedge input_2[1]
          or posedge input_3 or posedge input_4 or posedge input_5 or posedge input_6 or posedge input_7 or posedge input_8)
        (input_1 == 4'd7 && $stable(input_2[0]) && $changed(input_2[1])) |-> ##0 $stable(output_1)
    );

endmodule