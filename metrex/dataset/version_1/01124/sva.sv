// SVA checker for m_4to1_2bit_mux
module m_4to1_2bit_mux_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [1:0]  w_bus_mux_out,
  input  logic [1:0]  w_bus_mux_in_0,
  input  logic [1:0]  w_bus_mux_in_1,
  input  logic [1:0]  w_bus_mux_in_2,
  input  logic [1:0]  w_bus_mux_in_3,
  input  logic [1:0]  w_channel
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional equivalence
  A_FUNC_MAP: assert property (
    w_bus_mux_out == (w_channel==2'b00 ? w_bus_mux_in_0 :
                      w_channel==2'b01 ? w_bus_mux_in_1 :
                      w_channel==2'b10 ? w_bus_mux_in_2 :
                                         w_bus_mux_in_3)
  );

  // No X/Z on output when all controls/data are known
  A_NO_X_ON_OUT_WHEN_INPUTS_KNOWN: assert property (
    !$isunknown({w_channel, w_bus_mux_in_0, w_bus_mux_in_1, w_bus_mux_in_2, w_bus_mux_in_3})
    |-> !$isunknown(w_bus_mux_out)
  );

  // Output stability when inputs and select are stable (combinational sanity)
  A_STABLE_IF_INPUTS_STABLE: assert property (
    $stable({w_channel, w_bus_mux_in_0, w_bus_mux_in_1, w_bus_mux_in_2, w_bus_mux_in_3})
    |=> $stable(w_bus_mux_out)
  );

  // Coverage: each select path observed and correct
  C_CH0: cover property (w_channel==2'b00 && w_bus_mux_out==w_bus_mux_in_0);
  C_CH1: cover property (w_channel==2'b01 && w_bus_mux_out==w_bus_mux_in_1);
  C_CH2: cover property (w_channel==2'b10 && w_bus_mux_out==w_bus_mux_in_2);
  C_CH3: cover property (w_channel==2'b11 && w_bus_mux_out==w_bus_mux_in_3);

  // Coverage: sweep through all channels (any orderable stimulus)
  C_CHANNEL_SWEEP: cover property (
    (w_channel==2'b00) ##1 (w_channel==2'b01) ##1 (w_channel==2'b10) ##1 (w_channel==2'b11)
  );

endmodule

// Example bind (provide clk/rst_n from your env):
// bind m_4to1_2bit_mux m_4to1_2bit_mux_sva sva_inst(.clk(tb_clk), .rst_n(tb_rst_n), .*);