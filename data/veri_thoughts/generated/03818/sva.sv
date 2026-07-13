module priority_encoder_sva (
    input logic clk,
    input logic [254:0] in,
    input logic [7:0] out
);

    // Exact 0xFF low-byte pattern maps to 255.
    check_ff_maps_to_255: assert property (
        @(posedge clk)
        ((in[254:8] == 247'd0) && (in[7:0] == 8'hFF)) |-> (out == 8'd255)
    );

    // Exact 0xFE low-byte pattern maps to 254.
    check_fe_maps_to_254: assert property (
        @(posedge clk)
        ((in[254:8] == 247'd0) && (in[7:0] == 8'hFE)) |-> (out == 8'd254)
    );

    // Exact 0xFC low-byte pattern maps to 253.
    check_fc_maps_to_253: assert property (
        @(posedge clk)
        ((in[254:8] == 247'd0) && (in[7:0] == 8'hFC)) |-> (out == 8'd253)
    );

    // Exact 0xF8 low-byte pattern maps to 252.
    check_f8_maps_to_252: assert property (
        @(posedge clk)
        ((in[254:8] == 247'd0) && (in[7:0] == 8'hF8)) |-> (out == 8'd252)
    );

    // Exact 0xF0 low-byte pattern maps to 251.
    check_f0_maps_to_251: assert property (
        @(posedge clk)
        ((in[254:8] == 247'd0) && (in[7:0] == 8'hF0)) |-> (out == 8'd251)
    );

    // Exact 0xE0 low-byte pattern maps to 250.
    check_e0_maps_to_250: assert property (
        @(posedge clk)
        ((in[254:8] == 247'd0) && (in[7:0] == 8'hE0)) |-> (out == 8'd250)
    );

    // Any unlisted input pattern maps to 0.
    check_default_maps_to_0: assert property (
        @(posedge clk)
        !((in[254:8] == 247'd0) &&
          ((in[7:0] == 8'hFF) ||
           (in[7:0] == 8'hFE) ||
           (in[7:0] == 8'hFC) ||
           (in[7:0] == 8'hF8) ||
           (in[7:0] == 8'hF0) ||
           (in[7:0] == 8'hE0))) |-> (out == 8'd0)
    );

endmodule