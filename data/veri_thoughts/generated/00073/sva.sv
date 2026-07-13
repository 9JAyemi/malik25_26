module db_lut_beta_sva (
    input logic       clk,
    input logic [5:0] qp_i,
    input logic [6:0] beta_o
);

    // Inputs below 16 return the default value 0.
    check_default_below_16: assert property (
        @(posedge clk) (qp_i < 6'd16) |-> (beta_o == 7'd0)
    );

    // Inputs 16 through 28 map to qp_i minus 10.
    check_linear_map_16_to_28: assert property (
        @(posedge clk) ((qp_i >= 6'd16) && (qp_i <= 6'd28)) |-> (beta_o == ({1'b0, qp_i} - 7'd10))
    );

    // The first entry of the upper segment maps 29 to 20.
    check_boundary_29_maps_to_20: assert property (
        @(posedge clk) (qp_i == 6'd29) |-> (beta_o == 7'd20)
    );

    // Inputs 29 through 51 map to 2 * (qp_i - 19).
    check_even_map_29_to_51: assert property (
        @(posedge clk) ((qp_i >= 6'd29) && (qp_i <= 6'd51)) |-> (beta_o == (({1'b0, qp_i} - 7'd19) << 1))
    );

    // The highest explicit table entry maps 51 to 64.
    check_boundary_51_maps_to_64: assert property (
        @(posedge clk) (qp_i == 6'd51) |-> (beta_o == 7'd64)
    );

    // Inputs above 51 return the default value 0.
    check_default_above_51: assert property (
        @(posedge clk) (qp_i > 6'd51) |-> (beta_o == 7'd0)
    );

endmodule