module mux_sva (
    input logic CLK,
    input logic [3:0] ABCD,
    input logic [1:0] SEL,
    input logic EN,
    input logic Y
);
    // No clock/reset in RTL; pure combinational mux. Assertions sampled on external CLK.

    // EN low forces Y to 0.
    en_low_forces_y_zero: assert property (
        @(posedge CLK) (EN == 1'b0) |-> (Y == 1'b0)
    );

    // With EN high and SEL==00, Y equals ABCD[0].
    sel_00_routes_bit0: assert property (
        @(posedge CLK) (EN == 1'b1 && SEL == 2'b00) |-> (Y == ABCD[0])
    );

    // With EN high and SEL==01, Y equals ABCD[1].
    sel_01_routes_bit1: assert property (
        @(posedge CLK) (EN == 1'b1 && SEL == 2'b01) |-> (Y == ABCD[1])
    );

    // With EN high and SEL==10, Y equals ABCD[2].
    sel_10_routes_bit2: assert property (
        @(posedge CLK) (EN == 1'b1 && SEL == 2'b10) |-> (Y == ABCD[2])
    );

    // With EN high and SEL==11, Y equals ABCD[3].
    sel_11_routes_bit3: assert property (
        @(posedge CLK) (EN == 1'b1 && SEL == 2'b11) |-> (Y == ABCD[3])
    );

    // With EN high and unknown SEL, Y drives X (default case).
    unknown_sel_drives_x_when_en: assert property (
        @(posedge CLK) (EN == 1'b1 && $isunknown(SEL)) |-> (Y === 1'bx)
    );
endmodule