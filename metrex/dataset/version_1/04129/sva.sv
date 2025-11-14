// SVA for encryption_system
// Bindable, concise checks + key coverage

`ifndef SYNTHESIS
module encryption_system_sva (
  input logic              clk,
  input logic              reset,
  input logic [3:0]        data_in,
  input logic [3:0]        encrypted_data,
  input logic [3:0]        key,
  input logic [3:0]        adder_out,
  input logic [3:0]        shift_reg
);

  // past-valid tracking (cleared by reset)
  logic pv1, pv2;
  always_ff @(posedge clk) begin
    if (reset) begin
      pv1 <= 1'b0;
      pv2 <= 1'b0;
    end else begin
      pv1 <= 1'b1;
      pv2 <= pv1;
    end
  end

  // Synchronous reset behavior
  a_reset_sync: assert property (@(posedge clk)
    reset |-> (adder_out==4'b0 && shift_reg==4'b0 && encrypted_data==4'b0));

  // Key must be constant and known
  a_key_const: assert property (@(posedge clk)
    key == 4'b1010 && !$isunknown(key));

  // No X/Z on internal/outputs when active
  a_no_x_active: assert property (@(posedge clk) disable iff (reset)
    !$isunknown({adder_out, shift_reg, encrypted_data}));

  // Stage correctness
  a_adder: assert property (@(posedge clk) disable iff (reset)
    adder_out == (data_in + 4'b1010));

  a_shift: assert property (@(posedge clk)
    (pv1 && !reset) |-> (shift_reg == { $past(adder_out)[2:0], 1'b0 }));

  a_out_pipe: assert property (@(posedge clk)
    (pv1 && !reset) |-> (encrypted_data == $past(shift_reg)));

  // End-to-end 2-cycle functional check
  a_e2e_2cyc: assert property (@(posedge clk)
    (pv2 && !reset) |-> (encrypted_data == { (($past(data_in,2)+4'b1010)[2:0]), 1'b0 }));

  // Coverage
  c_nonzero_out: cover property (@(posedge clk)
    pv2 && !reset && (encrypted_data != 4'b0000));

  c_add_overflow: cover property (@(posedge clk)
    !reset && ({1'b0, data_in} + 5'b0_1010)[4]); // carry-out from add

  c_shift_drop_msb: cover property (@(posedge clk)
    pv1 && !reset && $past(adder_out)[3] &&
    (shift_reg == { $past(adder_out)[2:0], 1'b0 }));

endmodule

bind encryption_system encryption_system_sva u_encryption_system_sva(.*);
`endif