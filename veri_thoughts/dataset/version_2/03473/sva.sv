module bit_counter_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [3:0] out
);

    // out matches the implemented sum of the selected input slices.
    check_output_matches_rtl_sum: assert property (
        @(posedge clk)
        out == (
            in +
            {2'b00, in[3:2]} +
            {2'b00, in[2:1]} +
            {2'b00, in[1:0]} +
            {1'b0,  in[3:1]} +
            {1'b0,  in[2:0]} +
            {2'b00, in[3], in[1]} +
            {2'b00, in[2], in[0]}
        )
    );

    // Lower bits 000 produce 0 regardless of in[3].
    check_lower3_000_maps_to_0: assert property (
        @(posedge clk)
        (in[2:0] == 3'b000) |-> (out == 4'h0)
    );

    // Lower bits 001 produce 4 regardless of in[3].
    check_lower3_001_maps_to_4: assert property (
        @(posedge clk)
        (in[2:0] == 3'b001) |-> (out == 4'h4)
    );

    // Lower bits 010 produce 9 regardless of in[3].
    check_lower3_010_maps_to_9: assert property (
        @(posedge clk)
        (in[2:0] == 3'b010) |-> (out == 4'h9)
    );

    // Lower bits 011 produce D regardless of in[3].
    check_lower3_011_maps_to_d: assert property (
        @(posedge clk)
        (in[2:0] == 3'b011) |-> (out == 4'hD)
    );

    // Lower bits 100 produce F regardless of in[3].
    check_lower3_100_maps_to_f: assert property (
        @(posedge clk)
        (in[2:0] == 3'b100) |-> (out == 4'hF)
    );

    // Lower bits 101 produce 3 regardless of in[3].
    check_lower3_101_maps_to_3: assert property (
        @(posedge clk)
        (in[2:0] == 3'b101) |-> (out == 4'h3)
    );

    // Lower bits 110 produce 8 regardless of in[3].
    check_lower3_110_maps_to_8: assert property (
        @(posedge clk)
        (in[2:0] == 3'b110) |-> (out == 4'h8)
    );

    // Lower bits 111 produce C regardless of in[3].
    check_lower3_111_maps_to_c: assert property (
        @(posedge clk)
        (in[2:0] == 3'b111) |-> (out == 4'hC)
    );

    // Toggling only in[3] does not change out.
    check_msb_toggle_does_not_change_output: assert property (
        @(posedge clk)
        (!$initstate && (in[2:0] == $past(in[2:0])) && (in[3] != $past(in[3]))) |-> (out == $past(out))
    );

endmodule