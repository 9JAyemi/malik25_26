module signal_processor_sva (
    input  logic clk,
    input  logic [3:0] in,
    input  logic [3:0] out
);
    // For inputs 0..3, output equals in*2 modulo 16.
    check_map_in_lt4: assert property (
        @(posedge clk) (in < 4'd4) |-> (out == ((in * 4'd2)[3:0]))
    );

    // For inputs 4..7, output equals in*in modulo 16.
    check_map_in_4_to_7: assert property (
        @(posedge clk) ((in >= 4'd4) && (in <= 4'd7)) |-> (out == ((in * in)[3:0]))
    );

    // For inputs 8..15, output equals in/2.
    check_map_in_gt7: assert property (
        @(posedge clk) (in > 4'd7) |-> (out == (in / 4'd2))
    );

    // For inputs 0..3, output LSB is 0 (even result from multiply-by-2).
    check_even_out_when_lt4: assert property (
        @(posedge clk) (in < 4'd4) |-> (out[0] == 1'b0)
    );

    // Boundary: in==3 -> out==6.
    check_boundary_in_eq_3: assert property (
        @(posedge clk) (in == 4'd3) |-> (out == 4'd6)
    );

    // Boundary: in==4 -> out==0 (16 mod 16).
    check_boundary_in_eq_4: assert property (
        @(posedge clk) (in == 4'd4) |-> (out == 4'd0)
    );

    // Boundary: in==8 -> out==4 (8/2).
    check_boundary_in_eq_8: assert property (
        @(posedge clk) (in == 4'd8) |-> (out == 4'd4)
    );
endmodule