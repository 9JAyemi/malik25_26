// SVA for timecode_memory_interface
module timecode_memory_interface_sva
  #(parameter DATA_W=8, ADDR_W=13)
  (
    input  logic                    clk,
    input  logic                    reset,
    input  logic [DATA_W-1:0]       timecode_data,
    input  logic                    timecode_valid,
    input  logic [ADDR_W-1:0]       timecode_address,
    input  logic [DATA_W-1:0]       data_out,
    input  logic                    write_enable,
    // internal regs
    input  logic [DATA_W-1:0]       memory_data,
    input  logic [ADDR_W-1:0]       memory_address,
    input  logic                    memory_write_enable
  );

  // Known/clean outputs and internal regs when not in reset
  a_known: assert property (@(posedge clk) disable iff (reset)
    !$isunknown({write_enable, data_out, memory_write_enable, memory_data, memory_address})
  );

  // Reset behavior
  a_reset_clears_next: assert property (@(posedge clk)
    reset |=> (memory_data=='0 && memory_address=='0 && memory_write_enable==1'b0 &&
               data_out=='0 && write_enable==1'b0)
  );
  a_reset_holds_zero: assert property (@(posedge clk)
    reset && $past(reset) |-> (memory_data=='0 && memory_address=='0 && memory_write_enable==1'b0 &&
                               data_out=='0 && write_enable==1'b0)
  );

  // Address mirrors input (1-cycle latency due to NBA)
  a_addr_delay: assert property (@(posedge clk) disable iff (reset)
    $past(!reset) |-> memory_address == $past(timecode_address)
  );

  // Memory write-enable tracks timecode_valid (1-cycle latency)
  a_mwe_delay: assert property (@(posedge clk) disable iff (reset)
    $past(!reset) |-> memory_write_enable == $past(timecode_valid)
  );

  // On write cycle: capture data/address for next cycle
  a_mem_data_cap: assert property (@(posedge clk) disable iff (reset)
    timecode_valid |=> memory_data == $past(timecode_data)
  );
  a_mem_addr_cap: assert property (@(posedge clk) disable iff (reset)
    timecode_valid |=> memory_address == $past(timecode_address)
  );

  // On read cycle: outputs reflect previous internal state
  a_read_outputs_from_prev_internal: assert property (@(posedge clk) disable iff (reset)
    $past(!reset) && !timecode_valid |-> (data_out == $past(memory_data) &&
                                          write_enable == $past(memory_write_enable))
  );

  // memory_data does not change on read cycles
  a_mem_data_stable_on_read: assert property (@(posedge clk) disable iff (reset)
    !timecode_valid |-> $stable(memory_data)
  );

  // Outputs do not change during write cycles (they're not assigned)
  a_outputs_stable_on_write: assert property (@(posedge clk) disable iff (reset)
    timecode_valid |-> ($stable(data_out) && $stable(write_enable))
  );

  // If write_enable is asserted, it must be a read cycle following a write
  a_we_implies_prev_write: assert property (@(posedge clk) disable iff (reset)
    write_enable |-> (!timecode_valid && $past(timecode_valid))
  );

  // Key functional covers
  c_write_then_read_obs: cover property (@(posedge clk) disable iff (reset)
    $past(timecode_valid) && !timecode_valid && write_enable &&
    data_out == $past(timecode_data)
  );

  c_two_writes_then_read: cover property (@(posedge clk) disable iff (reset)
    timecode_valid ##1 timecode_valid ##1 !timecode_valid &&
    data_out == $past(timecode_data)
  );

  c_reset_write_read: cover property (@(posedge clk)
    $fell(reset) ##1 timecode_valid ##1 !timecode_valid
  );

endmodule

// Example bind (place in a testbench or a separate bind file):
// bind timecode_memory_interface
//   timecode_memory_interface_sva #(.DATA_W(8), .ADDR_W(13)) u_sva (
//     .clk(clk),
//     .reset(reset),
//     .timecode_data(timecode_data),
//     .timecode_valid(timecode_valid),
//     .timecode_address(timecode_address),
//     .data_out(data_out),
//     .write_enable(write_enable),
//     .memory_data(memory_data),
//     .memory_address(memory_address),
//     .memory_write_enable(memory_write_enable)
//   );