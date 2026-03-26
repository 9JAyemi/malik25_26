module input_to_output_sva (
    input logic        clk,
    input logic [3:0]  in,
    input logic [15:0] out
);

    // Input 0 maps to 0x0000 on the next clock.
    check_in_0_maps_out_0000: assert property (
        @(posedge clk) (in == 4'h0) |=> (out == 16'h0000)
    );

    // Input 1 maps to 0x1111 on the next clock.
    check_in_1_maps_out_1111: assert property (
        @(posedge clk) (in == 4'h1) |=> (out == 16'h1111)
    );

    // Input 2 maps to 0x0101 on the next clock.
    check_in_2_maps_out_0101: assert property (
        @(posedge clk) (in == 4'h2) |=> (out == 16'h0101)
    );

    // Input 3 maps to 0x1010 on the next clock.
    check_in_3_maps_out_1010: assert property (
        @(posedge clk) (in == 4'h3) |=> (out == 16'h1010)
    );

    // Input 4 maps to 0x0011 on the next clock.
    check_in_4_maps_out_0011: assert property (
        @(posedge clk) (in == 4'h4) |=> (out == 16'h0011)
    );

    // Input 5 maps to 0x1100 on the next clock.
    check_in_5_maps_out_1100: assert property (
        @(posedge clk) (in == 4'h5) |=> (out == 16'h1100)
    );

    // Input 6 maps to 0x0110 on the next clock.
    check_in_6_maps_out_0110: assert property (
        @(posedge clk) (in == 4'h6) |=> (out == 16'h0110)
    );

    // Input 7 maps to 0x1001 on the next clock.
    check_in_7_maps_out_1001: assert property (
        @(posedge clk) (in == 4'h7) |=> (out == 16'h1001)
    );

    // Input 8 maps to 0x1111 on the next clock.
    check_in_8_maps_out_1111: assert property (
        @(posedge clk) (in == 4'h8) |=> (out == 16'h1111)
    );

    // Input 9 maps to 0x0000 on the next clock.
    check_in_9_maps_out_0000: assert property (
        @(posedge clk) (in == 4'h9) |=> (out == 16'h0000)
    );

    // Input A maps to 0x1010 on the next clock.
    check_in_a_maps_out_1010: assert property (
        @(posedge clk) (in == 4'hA) |=> (out == 16'h1010)
    );

    // Input B maps to 0x0101 on the next clock.
    check_in_b_maps_out_0101: assert property (
        @(posedge clk) (in == 4'hB) |=> (out == 16'h0101)
    );

    // Input C maps to 0x1100 on the next clock.
    check_in_c_maps_out_1100: assert property (
        @(posedge clk) (in == 4'hC) |=> (out == 16'h1100)
    );

    // Input D maps to 0x0011 on the next clock.
    check_in_d_maps_out_0011: assert property (
        @(posedge clk) (in == 4'hD) |=> (out == 16'h0011)
    );

    // Input E maps to 0x1001 on the next clock.
    check_in_e_maps_out_1001: assert property (
        @(posedge clk) (in == 4'hE) |=> (out == 16'h1001)
    );

    // Input F maps to 0x0110 on the next clock.
    check_in_f_maps_out_0110: assert property (
        @(posedge clk) (in == 4'hF) |=> (out == 16'h0110)
    );

endmodule