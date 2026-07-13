module counter_sva (
    input logic clk,
    input logic rst,
    output logic [7:0] value
);
    // Counter increments on each clock cycle
    increment: assert property (
        @(posedge clk) disable iff (!rst) ctr_q + 1'b1 == ctr_d
    );
    
    // Counter value is updated on each clock cycle
    update_value: assert property (
        @(posedge clk) disable iff (!rst) value == (ctr_q[CTR_LEN-1] == 1'b1 ? ~ctr_q[CTR_LEN-2:CTR_LEN-9] : ctr_q[CTR_LEN-2:CTR_LEN-9])
    );
    
    // Counter resets to zero on reset
    reset_to_zero: assert property (
        @(posedge clk) disable iff (!rst) rst |-> ctr_q == 'b0
    );
    
    // Counter value is within valid range
    valid_value_range: assert property (
        @(posedge clk) disable iff (!rst) (value >= 8'b00000000 && value <= 8'b11111111)
    );
    
    // Counter increments on each clock cycle
    increment_check: assert property (
        @(posedge clk) disable iff (!rst) ctr_q + 1'b1 == ctr_d
    );
    
    // Counter value is updated on each clock cycle
    update_value_check: assert property (
        @(posedge clk) disable iff (!rst) value == (ctr_q[CTR_LEN-1] == 1'b1 ? ~ctr_q[CTR_LEN-2:CTR_LEN-9] : ctr_q[CTR_LEN-2:CTR_LEN-9])
    );
    
    // Counter resets to zero on reset
    reset_to_zero_check: assert property (
        @(posedge clk) disable iff (!rst) rst |-> ctr_q == 'b0
    );
    
    // Counter value is within valid range
    valid_value_range_check: assert property (
        @(posedge clk) disable iff (!rst) (value >= 8'b00000000 && value <= 8'b11111111)
    );
endmodule