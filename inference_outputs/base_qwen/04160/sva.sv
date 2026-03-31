```systemverilog
module gray_shift_register_sva (
    input CLK,
    input RST,
    input [7:0] data_in,
    input shift,
    input load,
    input select,
    output reg [7:0] shift_reg_out,
    output reg [7:0] counter_out,
    output reg [7:0] final_output
);
    // Sequential logic assertions
    // Shift register increments on each clock cycle
    shift_reg_increment: assert property (
        @(posedge CLK) disable iff (!RST) shift_reg_out == shift_reg + 1
    );
    // Gray counter increments on each clock cycle
    gray_counter_increment: assert property (
        @(posedge CLK) disable iff (!RST) counter_out == gray_counter_out + 1
    );
    // Shift register loads data_in when load is asserted
    shift_reg_load: assert property (
        @(posedge CLK) disable iff (!RST) (load == 1'b1) |-> shift_reg_out == data_in
    );
    // Shift register shifts left when shift is asserted
    shift_reg_shift: assert property (
        @(posedge CLK) disable iff (!RST) (shift == 1'b1) |-> shift_reg_out == {shift_reg_out[6:0], 1'b0}
    );
    // Final output selects between shift register and counter
    final_output_select: assert property (
        @(posedge CLK) disable iff (!RST) final_output == (select == 1'b1) ? shift_reg_out : counter_out
    );

    // Combinational logic assertions
    // Counter output is the XOR of the gray counter and its right shift
    counter_output_comb: assert property (
        @(posedge CLK) disable iff (!RST) counter_out == (gray_counter_out ^ (gray_counter_out >> 1))
    );
    // Shift register output is the XOR of the shift register and its right shift
    shift_reg_output_comb: assert property (
        @(posedge CLK) disable iff (!RST) shift_reg_out == (shift_reg ^ (shift_reg >> 1))
    );
endmodule
```