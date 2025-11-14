// SVA for regfile
// Bind this checker to the DUT
module regfile_sva (
  input logic         clk,
  input logic         wr_en,
  input logic [2:0]   wr_addr,
  input logic [2:0]   rd_addr,
  input logic [31:0]  wr_data,
  input logic [31:0]  rd_data,
  input logic [1:0]   rd_guards,
  input logic [1:0]   rd_guardsok
);
  // Access DUT internals via bind scope: registers[0:7]

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Combinational equivalences (continuous read datapath and guards)
  always @* begin
    assert (rd_data === registers[rd_addr])
      else $error("rd_data != registers[rd_addr]");
    assert (rd_guards   === {rd_data[0], 1'b1})
      else $error("rd_guards mapping wrong");
    assert (rd_guardsok === {1'b1, rd_data[0]})
      else $error("rd_guardsok mapping wrong");
    assert (rd_guards === rd_guardsok)
      else $error("rd_guards != rd_guardsok");
    assert (rd_guards[0]  === 1'b1 && rd_guardsok[0] === 1'b1)
      else $error("constant guard bit not 1");
  end

  // Write updates targeted entry with written data (1-cycle later sample)
  a_write_updates_target: assert property (
    disable iff (!past_valid)
    wr_en |=> registers[$past(wr_addr)] == $past(wr_data)
  ) else $error("Write did not update targeted register with wr_data");

  // No unintended changes
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_reg_stability
      // If no write, all registers hold
      a_stable_when_no_write: assert property (
        disable iff (!past_valid)
        !wr_en |=> $stable(registers[i])
      ) else $error("Register %0d changed without write", i);

      // On write, only targeted index may change
      a_others_stable_on_write: assert property (
        disable iff (!past_valid)
        wr_en && (wr_addr != i) |=> $stable(registers[i])
      ) else $error("Non-target register %0d changed on write", i);
    end
  endgenerate

  // Basic sanity on addresses when used
  a_wr_addr_known_when_writing: assert property (
    wr_en |-> !$isunknown(wr_addr)
  ) else $error("wr_addr X/Z when writing");

  a_rd_addr_known: assert property (
    !$isunknown(rd_addr)
  ) else $error("rd_addr X/Z");

  // Coverage
  generate
    for (i = 0; i < 8; i++) begin : g_cov
      c_write_each_addr: cover property (wr_en && wr_addr == i);
      c_read_each_addr:  cover property (rd_addr == i);
    end
  endgenerate

  c_same_cycle_write_and_read_same_addr: cover property (wr_en && (rd_addr == wr_addr));
  c_write_then_read_same_addr_next:      cover property (wr_en ##1 (rd_addr == $past(wr_addr)));
  c_guard_lsb_0_to_1:                    cover property (rd_data[0]==1'b0 ##1 rd_data[0]==1'b1);
  c_guard_lsb_1_to_0:                    cover property (rd_data[0]==1'b1 ##1 rd_data[0]==1'b0);

endmodule

bind regfile regfile_sva sva_inst (.*);