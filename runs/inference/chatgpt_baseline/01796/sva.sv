module mem_encrypt_decrypt_sva (
  input logic clk,
  input logic reset,
  input logic [7:0] data_in,
  input logic [7:0] key,
  input logic enable,
  input logic [7:0] data_out,
  input logic [7:0] encrypted_data
);
  // Reset drives data_out and encrypted_data to zero.
  reset_clears_regs: assert property (
    @(posedge clk) reset |-> (data_out == 8'h00) && (encrypted_data == 8'h00)
  );

  // With enable=0, encrypted_data holds its value to the next cycle.
  en0_holds_encrypted: assert property (
    @(posedge clk) disable iff (reset) (!enable) |=> (encrypted_data == $past(encrypted_data))
  );

  // With enable=1, encrypted_data updates to data_in ^ key on the next cycle.
  en1_updates_encrypted: assert property (
    @(posedge clk) disable iff (reset) (enable) |=> (encrypted_data == ($past(data_in) ^ $past(key)))
  );

  // With enable=0, data_out passes through data_in on the next cycle.
  en0_bypass_data_out: assert property (
    @(posedge clk) disable iff (reset) (!enable) |=> (data_out == $past(data_in))
  );

  // With enable=1, data_out takes the previous encrypted_data on the next cycle.
  en1_pipeline_data_out: assert property (
    @(posedge clk) disable iff (reset) (enable) |=> (data_out == $past(encrypted_data))
  );

  // Each cycle after reset, data_out equals the previous cycle's muxed source.
  data_out_prev_mux: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (data_out == ($past(enable) ? $past(encrypted_data) : $past(data_in)))
  );

  // Each cycle after reset, encrypted_data equals the previous cycle's selected update.
  encrypted_prev_mux: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (encrypted_data == ($past(enable) ? ($past(data_in) ^ $past(key)) : $past(encrypted_data)))
  );

  // Back-to-back enable cycles propagate the first cycle's XOR to data_out two cycles later.
  back_to_back_enable_pipeline: assert property (
    @(posedge clk) disable iff (reset) (enable ##1 enable) |=> (data_out == $past(data_in ^ key, 2))
  );
endmodule