// SVA for reg_file: concise, high-quality checks and essential coverage

module reg_file_sva #(parameter int n = 8, w = 8) (
  input  logic                 clk,
  input  logic                 wr_en,
  input  logic                 rd_en,
  input  logic [4:0]           addr1,
  input  logic [4:0]           addr2,
  input  logic [w-1:0]         data_in,
  input  logic [w-1:0]         data1,
  input  logic [w-1:0]         data2,
  input  logic [w-1:0]         registers [0:n-1]
);

  // Track valid past for $past-based properties
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  function automatic bit in_range_addr (logic [4:0] a);
    return a < n;
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Basic well-formedness
  a_ctrl_no_x: assert property (cb !$isunknown({wr_en, rd_en, addr1, addr2}))
    else $error("reg_file: X/Z on control/address");

  a_addr_in_range_on_use_wr: assert property (cb wr_en |-> in_range_addr(addr1))
    else $error("reg_file: write addr1 out of range");
  a_addr_in_range_on_use_rd: assert property (cb rd_en |-> (in_range_addr(addr1) && in_range_addr(addr2)))
    else $error("reg_file: read addr out of range");

  // Read datapath correctness and gating (sample after NBA with ##0)
  a_rd_disables_zero: assert property (cb !rd_en |-> ##0 (data1 == '0 && data2 == '0))
    else $error("reg_file: outputs not zero when rd_en=0");

  a_rd1_matches_array: assert property (cb rd_en && in_range_addr(addr1) |-> ##0 (data1 == registers[addr1]))
    else $error("reg_file: data1 != registers[addr1]");
  a_rd2_matches_array: assert property (cb rd_en && in_range_addr(addr2) |-> ##0 (data2 == registers[addr2]))
    else $error("reg_file: data2 != registers[addr2]");

  a_reads_equal_on_same_addr: assert property (cb rd_en && in_range_addr(addr1) && (addr1 == addr2) |-> ##0 (data1 == data2))
    else $error("reg_file: data1 != data2 when addr1==addr2");

  // Write semantics: update only the targeted element, preserve others
  a_wr_updates_target: assert property (cb disable iff (!past_valid)
                                       wr_en && in_range_addr(addr1)
                                       |=> registers[$past(addr1)] == $past(data_in))
    else $error("reg_file: written element not updated with data_in");

  genvar i;
  generate
    for (i = 0; i < n; i++) begin : g_preserve_others
      a_wr_preserves_others: assert property (cb disable iff (!past_valid)
                                             wr_en && in_range_addr(addr1) && ($past(addr1) != i)
                                             |=> registers[i] == $past(registers[i]))
        else $error("reg_file: non-target register %0d changed on write", i);
      a_no_wr_keeps_stable: assert property (cb disable iff (!past_valid)
                                            !wr_en |=> $stable(registers[i]))
        else $error("reg_file: register %0d changed without write", i);
    end
  endgenerate

  // Essential functional coverage
  c_two_reads_same_addr:   cover property (cb rd_en && in_range_addr(addr1) && addr1 == addr2);
  c_two_reads_diff_addr:   cover property (cb rd_en && in_range_addr(addr1) && in_range_addr(addr2) && addr1 != addr2);
  c_wr_then_rd_same_addr:  cover property (cb wr_en && in_range_addr(addr1) ##1 rd_en && (addr1 == $past(addr1)));
  c_back_to_back_writes:   cover property (cb wr_en && in_range_addr(addr1) ##1 wr_en && in_range_addr(addr1) && (addr1 != $past(addr1)));
  c_read_disabled_zeros:   cover property (cb !rd_en);
  c_access_low_high:       cover property (cb wr_en && addr1 == 0)
                         or cover property (cb wr_en && addr1 == n-1);

endmodule

// Bind into DUT; exposes internal array for strong checks
bind reg_file reg_file_sva #(.n(n), .w(w)) reg_file_sva_i (.*);