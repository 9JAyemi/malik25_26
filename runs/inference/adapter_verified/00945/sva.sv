module control_module_sva (
    input logic clk,
    input logic [3:0] input_1,
    input logic [1:0] input_2,
    input logic input_3,
    input logic input_4,
    input logic input_5,
    input logic input_6,
    input logic input_7,
    input logic input_8,
    input logic output_1
);

// input_1==0 forces output_1 low.
    check_map_0: assert property (
        @(posedge clk) (input_1 == 4'd0) |-> (output_1 == 1'b0)
    );

// input_1==1 selects input_3.
    check_map_1: assert property (
        @(posedge clk) (input_1 == 4'd1) |-> (output_1 == input_3)
    );

// input_1==2 selects input_4.
    check_map_2: assert property (
        @(posedge clk) (input_1 == 4'd2) |-> (output_1 == input_4)
    );

// input_1==3 selects input_5.
    check_map_3: assert property (
        @(posedge clk) (input_1 == 4'd3) |-> (output_1 == input_5)
    );

// input_1==4 selects input_6.
    check_map_4: assert property (
        @(posedge clk) (input_1 == 4'd4) |-> (output_1 == input_6)
    );

// input_1==5 selects input_7.
    check_map_5: assert property (
        @(posedge clk) (input_1 == 4'd5) |-> (output_1 == input_7)
    );

// input_1==6 selects input_8.
    check_map_6: assert property (
        @(posedge clk) (input_1 == 4'd6) |-> (output_1 == input_8)
    );

// input_1==7 selects input_2[0].
    check_map_7: assert property (
        @(posedge clk) (input_1 == 4'd7) |-> (output_1 == input_2[0])
    );

// input_1==8..15 drive output_1 low.
    check_map_default: assert property (
        @(posedge clk) (input_1 >= 4'd8) |-> (output_1 == 1'b0)
    );

endmodule
