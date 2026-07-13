module decoder_4to16_sva (
    input logic clk,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic EN,
    input logic [15:0] Y
);
    // Y must be all 1s next cycle when EN is low.
    check_y_all_ones_when_disabled: assert property (
        @(posedge clk) (!EN) |=> (Y == 16'hFFFF)
    );

    // When EN is high and {A,B}==0, Y must be 0xFFFE next cycle.
    check_decode_code0: assert property (
        @(posedge clk) (EN && ({A,B} == 4'b0000)) |=> (Y == 16'hFFFE)
    );

    // When EN is high and {A,B}==1, Y must be 0xFFFD next cycle.
    check_decode_code1: assert property (
        @(posedge clk) (EN && ({A,B} == 4'b0001)) |=> (Y == 16'hFFFD)
    );

    // When EN is high and {A,B}==2, Y must be 0xFFFB next cycle.
    check_decode_code2: assert property (
        @(posedge clk) (EN && ({A,B} == 4'b0010)) |=> (Y == 16'hFFFB)
    );

    // When EN is high and {A,B}==3, Y must be 0xFFF7 next cycle.
    check_decode_code3: assert property (
        @(posedge clk) (EN && ({A,B} == 4'b0011)) |=> (Y == 16'hFFF7)
    );

    // When EN is high and {A,B} not in 0..3, Y must be all 1s next cycle.
    check_default_all_ones_for_other_codes: assert property (
        @(posedge clk) (EN && !({A,B} inside {4'b0000,4'b0001,4'b0010,4'b0011})) |=> (Y == 16'hFFFF)
    );

    // On valid decode (0..3) with EN high, upper bits [15:4] must be all 1s next cycle.
    check_high_bits_ones_on_valid_decode: assert property (
        @(posedge clk) (EN && ({A,B} inside {4'b0000,4'b0001,4'b0010,4'b0011})) |=> (Y[15:4] == 12'hFFF)
    );

    // On valid decode (0..3) with EN high, Y is not 0xFFFF next cycle.
    check_not_all_ones_on_valid_decode: assert property (
        @(posedge clk) (EN && ({A,B} inside {4'b0000,4'b0001,4'b0010,4'b0011})) |=> (Y != 16'hFFFF)
    );
endmodule