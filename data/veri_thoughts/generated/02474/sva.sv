module Valid_Monitor_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] Valid,
    input logic [3:0] FE_ID
);
    // FE_ID must be 0 while reset is asserted (active-low async reset).
    reset_fe_id_zero: assert property (
        @(posedge clk) !rst_n |-> (FE_ID == 4'h0)
    );

    // If Valid[0] is 1, FE_ID must be 1.
    map_bit0_to_id1: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[0] == 1'b1) |-> (FE_ID == 4'h1)
    );

    // If Valid[1] is 1 and Valid[0] is 0, FE_ID must be 2.
    map_bit1_to_id2: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[1] && !Valid[0]) |-> (FE_ID == 4'h2)
    );

    // If Valid[2] is 1 and Valid[1:0] are 0, FE_ID must be 3.
    map_bit2_to_id3: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[2] && (Valid[1:0] == 2'b00)) |-> (FE_ID == 4'h3)
    );

    // If Valid[3] is 1 and Valid[2:0] are 0, FE_ID must be 4.
    map_bit3_to_id4: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[3] && (Valid[2:0] == 3'b000)) |-> (FE_ID == 4'h4)
    );

    // If Valid[4] is 1 and Valid[3:0] are 0, FE_ID must be 5.
    map_bit4_to_id5: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[4] && (Valid[3:0] == 4'b0000)) |-> (FE_ID == 4'h5)
    );

    // If Valid[5] is 1 and Valid[4:0] are 0, FE_ID must be 6.
    map_bit5_to_id6: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[5] && (Valid[4:0] == 5'b00000)) |-> (FE_ID == 4'h6)
    );

    // If Valid[6] is 1 and Valid[5:0] are 0, FE_ID must be 7.
    map_bit6_to_id7: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[6] && (Valid[5:0] == 6'b000000)) |-> (FE_ID == 4'h7)
    );

    // If Valid[7] is 1 and Valid[6:0] are 0, FE_ID must be 8.
    map_bit7_to_id8: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid[7] && (Valid[6:0] == 7'b0000000)) |-> (FE_ID == 4'h8)
    );

    // When Valid is all zeros, FE_ID must be 0.
    zero_when_no_valids: assert property (
        @(posedge clk) disable iff (!rst_n) (Valid == 8'h00) |-> (FE_ID == 4'h0)
    );

    // FE_ID can only take values 0 through 8 when not in reset.
    id_value_range: assert property (
        @(posedge clk) disable iff (!rst_n) (FE_ID inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7,4'h8})
    );
endmodule