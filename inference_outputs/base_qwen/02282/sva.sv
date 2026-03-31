```systemverilog
module shift_register_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic shift_right,
    input logic load,
    output logic [3:0] data_out
);
    // Sequential logic for shift register stages
    // Stage1 should hold the value of data_in when load is asserted
    stage1_load: assert property (
        @(posedge clk) disable iff (!clk) load |-> (stage1 == data_in)
    );
    // Stage2 should hold the value of stage1 when load is asserted
    stage2_load: assert property (
        @(posedge clk) disable iff (!clk) load |-> (stage2 == stage1)
    );
    // Stage3 should hold the value of stage2 when load is asserted
    stage3_load: assert property (
        @(posedge clk) disable iff (!clk) load |-> (stage3 == stage2)
    );
    // Stage4 should hold the value of stage3 when load is asserted
    stage4_load: assert property (
        @(posedge clk) disable iff (!clk) load |-> (stage4 == stage3)
    );
    // Stage1 should hold the value of stage4 when shift_right is asserted and load is not asserted
    stage1_shift_right: assert property (
        @(posedge clk) disable iff (!clk) (shift_right && !load) |-> (stage1 == stage4)
    );
    // Stage2 should hold the value of stage1 when shift_right is asserted and load is not asserted
    stage2_shift_right: assert property (
        @(posedge clk) disable iff (!clk) (shift_right && !load) |-> (stage2 == stage1)
    );
    // Stage3 should hold the value of stage2 when shift_right is asserted and load is not asserted
    stage3_shift_right: assert property (
        @(posedge clk) disable iff (!clk) (shift_right && !load) |-> (stage3 == stage2)
    );
    // Stage4 should hold the value of data_in when shift_right is not asserted and load is not asserted
    stage4_shift_left: assert property (
        @(posedge clk) disable iff (!clk) (!shift_right && !load) |-> (stage4 == data_in)
    );
    // data_out should always be equal to stage4
    data_out_correct: assert property (
        @(posedge clk) disable iff (!clk) (data_out == stage4)
    );
endmodule
```