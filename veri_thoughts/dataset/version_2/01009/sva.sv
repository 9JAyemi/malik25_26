module priority_encoder_sva (
    input logic clk,
    input logic [3:0] inputs,
    input logic [1:0] outputs
);
    // Combinational DUT with no reset; sample assertions on clk.

    // 0001 maps to 00.
    map_0001_is_00: assert property (
        @(posedge clk) (inputs == 4'b0001) |=> (outputs == 2'b00)
    );

    // 0010 maps to 01.
    map_0010_is_01: assert property (
        @(posedge clk) (inputs == 4'b0010) |=> (outputs == 2'b01)
    );

    // 0100 maps to 10.
    map_0100_is_10: assert property (
        @(posedge clk) (inputs == 4'b0100) |=> (outputs == 2'b10)
    );

    // 1000 maps to 11.
    map_1000_is_11: assert property (
        @(posedge clk) (inputs == 4'b1000) |=> (outputs == 2'b11)
    );

    // 0011 maps to 10.
    map_0011_is_10: assert property (
        @(posedge clk) (inputs == 4'b0011) |=> (outputs == 2'b10)
    );

    // 0111 maps to 10.
    map_0111_is_10: assert property (
        @(posedge clk) (inputs == 4'b0111) |=> (outputs == 2'b10)
    );

    // 1110 maps to 10.
    map_1110_is_10: assert property (
        @(posedge clk) (inputs == 4'b1110) |=> (outputs == 2'b10)
    );

    // 1101 maps to 10.
    map_1101_is_10: assert property (
        @(posedge clk) (inputs == 4'b1101) |=> (outputs == 2'b10)
    );

    // 1011 maps to 10.
    map_1011_is_10: assert property (
        @(posedge clk) (inputs == 4'b1011) |=> (outputs == 2'b10)
    );

    // 0110 maps to 10.
    map_0110_is_10: assert property (
        @(posedge clk) (inputs == 4'b0110) |=> (outputs == 2'b10)
    );

    // Default-listed patterns map to 00.
    map_default_set_is_00: assert property (
        @(posedge clk) (inputs inside {4'b0000,4'b0101,4'b1001,4'b1010,4'b1100,4'b1111}) |=> (outputs == 2'b00)
    );
endmodule