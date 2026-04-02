module hpdmc_banktimer_sva (
    input logic sys_clk,
    input logic sdram_rst,
    input logic tim_cas,
    input logic [1:0] tim_wr,
    input logic read,
    input logic write,
    input logic precharge_safe
);
    // Counter should be reset to 0 on sdram_rst
    reset_counter: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) sdram_rst |-> (counter == 3'd0)
    );

    // Precharge_safe should be set to 1 on sdram_rst
    reset_precharge_safe: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) sdram_rst |-> (precharge_safe == 1'b1)
    );

    // Counter should be set to 4 when read is asserted
    read_counter_set: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) read |-> (counter == 3'd4)
    );

    // Precharge_safe should be set to 0 when read is asserted
    read_precharge_safe_set: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) read |-> (precharge_safe == 1'b0)
    );

    // Counter should be set to {1'b1, tim_wr} when write is asserted
    write_counter_set: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) write |-> (counter == {1'b1, tim_wr})
    );

    // Precharge_safe should be set to 0 when write is asserted
    write_precharge_safe_set: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) write |-> (precharge_safe == 1'b0)
    );

    // Counter should decrement when precharge_safe is 0 and counter is not 1
    decrement_counter: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) (precharge_safe == 1'b0) && (counter != 3'd1) |-> (counter == counter - 3'd1)
    );

    // Precharge_safe should be set to 1 when counter is 1 and precharge_safe is 0
    set_precharge_safe: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) (counter == 3'd1) && (precharge_safe == 1'b0) |-> (precharge_safe == 1'b1)
    );

    // Counter should not change when read and write are both asserted
    read_write_counter_stable: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) (read && write) |-> (counter == counter)
    );

    // Precharge_safe should not change when read and write are both asserted
    read_write_precharge_safe_stable: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) (read && write) |-> (precharge_safe == precharge_safe)
    );

    // Counter should not change when tim_cas is asserted
    tim_cas_counter_stable: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) tim_cas |-> (counter == counter)
    );

    // Precharge_safe should not change when tim_cas is asserted
    tim_cas_precharge_safe_stable: assert property (
        @(posedge sys_clk) disable iff (!sdram_rst) tim_cas |-> (precharge_safe == precharge_safe)
    );
endmodule