module decoder_sva (
    input  logic clk,
    input  logic A,
    input  logic B,
    input  logic EN,
    input  logic Y0,
    input  logic Y1,
    input  logic Y2,
    input  logic Y3
);
    // Outputs implement exact decoding function: EN ? (1 << {A,B}) : 0
    check_decode_function_vector: assert property (
        @(posedge clk) {Y3,Y2,Y1,Y0} == (EN ? (4'b0001 << {A,B}) : 4'b0000)
    );

    // When disabled, all outputs are 0
    check_disabled_all_zero: assert property (
        @(posedge clk) (EN == 1'b0) |-> ({Y3,Y2,Y1,Y0} == 4'b0000)
    );

    // When EN and AB==00, Y0=1 and others 0
    check_decode_00: assert property (
        @(posedge clk) (EN && (A==1'b0) && (B==1'b0)) |-> (Y0 && !Y1 && !Y2 && !Y3)
    );

    // When EN and AB==01, Y1=1 and others 0
    check_decode_01: assert property (
        @(posedge clk) (EN && (A==1'b0) && (B==1'b1)) |-> (!Y0 && Y1 && !Y2 && !Y3)
    );

    // When EN and AB==10, Y2=1 and others 0
    check_decode_10: assert property (
        @(posedge clk) (EN && (A==1'b1) && (B==1'b0)) |-> (!Y0 && !Y1 && Y2 && !Y3)
    );

    // When EN and AB==11, Y3=1 and others 0
    check_decode_11: assert property (
        @(posedge clk) (EN && (A==1'b1) && (B==1'b1)) |-> (!Y0 && !Y1 && !Y2 && Y3)
    );

    // At most one output is HIGH at any time (onehot0)
    check_outputs_onehot0: assert property (
        @(posedge clk) $onehot0({Y3,Y2,Y1,Y0})
    );

    // The OR of outputs equals EN
    check_outputs_or_equals_en: assert property (
        @(posedge clk) ((Y0 || Y1 || Y2 || Y3) == EN)
    );

    // If Y0 is HIGH, decoder must be enabled and AB==00
    check_y0_implies_en_ab00: assert property (
        @(posedge clk) Y0 |-> (EN && (A==1'b0) && (B==1'b0))
    );

    // If Y3 is HIGH, decoder must be enabled and AB==11
    check_y3_implies_en_ab11: assert property (
        @(posedge clk) Y3 |-> (EN && (A==1'b1) && (B==1'b1))
    );
endmodule