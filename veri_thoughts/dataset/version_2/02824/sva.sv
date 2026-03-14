module multiplexer_sva (
    input  logic        clk,
    input  logic [5:0]  in1,
    input  logic [5:0]  in2,
    input  logic [5:0]  in3,
    input  logic [5:0]  in4,
    input  logic [5:0]  in5,
    input  logic [5:0]  in6,
    input  logic [5:0]  in7,
    input  logic [5:0]  in8,
    input  logic [5:0]  in9,
    input  logic [5:0]  in10,
    input  logic [5:0]  in11,
    input  logic [5:0]  in12,
    input  logic [5:0]  in13,
    input  logic [5:0]  in14,
    input  logic [5:0]  in15,
    input  logic [5:0]  in16,
    input  logic [3:0]  sel,
    input  logic [5:0]  out
);

    ///// Multiplexer selection mapping /////
    // When sel=0000, out equals in1.
    mux_map_sel_0000_to_in1: assert property (
        @(posedge clk) (sel == 4'b0000) |-> (out == in1)
    );
    // When sel=0001, out equals in2.
    mux_map_sel_0001_to_in2: assert property (
        @(posedge clk) (sel == 4'b0001) |-> (out == in2)
    );
    // When sel=0010, out equals in3.
    mux_map_sel_0010_to_in3: assert property (
        @(posedge clk) (sel == 4'b0010) |-> (out == in3)
    );
    // When sel=0011, out equals in4.
    mux_map_sel_0011_to_in4: assert property (
        @(posedge clk) (sel == 4'b0011) |-> (out == in4)
    );
    // When sel=0100, out equals in5.
    mux_map_sel_0100_to_in5: assert property (
        @(posedge clk) (sel == 4'b0100) |-> (out == in5)
    );
    // When sel=0101, out equals in6.
    mux_map_sel_0101_to_in6: assert property (
        @(posedge clk) (sel == 4'b0101) |-> (out == in6)
    );
    // When sel=0110, out equals in7.
    mux_map_sel_0110_to_in7: assert property (
        @(posedge clk) (sel == 4'b0110) |-> (out == in7)
    );
    // When sel=0111, out equals in8.
    mux_map_sel_0111_to_in8: assert property (
        @(posedge clk) (sel == 4'b0111) |-> (out == in8)
    );
    // When sel=1000, out equals in9.
    mux_map_sel_1000_to_in9: assert property (
        @(posedge clk) (sel == 4'b1000) |-> (out == in9)
    );
    // When sel=1001, out equals in10.
    mux_map_sel_1001_to_in10: assert property (
        @(posedge clk) (sel == 4'b1001) |-> (out == in10)
    );
    // When sel=1010, out equals in11.
    mux_map_sel_1010_to_in11: assert property (
        @(posedge clk) (sel == 4'b1010) |-> (out == in11)
    );
    // When sel=1011, out equals in12.
    mux_map_sel_1011_to_in12: assert property (
        @(posedge clk) (sel == 4'b1011) |-> (out == in12)
    );
    // When sel=1100, out equals in13.
    mux_map_sel_1100_to_in13: assert property (
        @(posedge clk) (sel == 4'b1100) |-> (out == in13)
    );
    // When sel=1101, out equals in14.
    mux_map_sel_1101_to_in14: assert property (
        @(posedge clk) (sel == 4'b1101) |-> (out == in14)
    );
    // When sel=1110, out equals in15.
    mux_map_sel_1110_to_in15: assert property (
        @(posedge clk) (sel == 4'b1110) |-> (out == in15)
    );
    // When sel=1111, out equals in16.
    mux_map_sel_1111_to_in16: assert property (
        @(posedge clk) (sel == 4'b1111) |-> (out == in16)
    );

    ///// Combinational stability /////
    // If all inputs and sel are stable between cycles, out is stable.
    mux_stable_when_all_inputs_and_sel_stable: assert property (
        @(posedge clk) $stable({in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,sel}) |-> $stable(out)
    );

endmodule