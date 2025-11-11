// SVA for RegFileWW
// Bind these assertions to the DUT (no DUT/testbench edits needed)

module RegFileWW_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,wren,rd1en,rd2en,wrbyteen,wraddr,rd1addr,rd2addr,wrdata}));

  // Helpers
  function automatic bit is_prefix_ones (logic [15:0] be);
    // 1,3,7,0xF, ... 0xFFFF  => be != 0 and be&(be+1)==0
    is_prefix_ones = (be != 16'h0) && (((be & (be + 16'h1)) == 16'h0));
  endfunction

  function automatic int unsigned byte_idx (logic [15:0] be);
    // be = 2^(idx+1)-1  => idx = clog2(be+1)-1
    byte_idx = $clog2(be + 16'h1) - 1;
  endfunction

  function automatic logic [7:0] sel_byte (logic [0:127] d, int unsigned i);
    sel_byte = d[i*8 +: 8]; // wrdata is [0:127]
  endfunction

  // Ones generator must be all ones every cycle
  assert property (1 |-> ones == {128{1'b1}});

  // Operand selection on legal write mask
  assert property ((wren && is_prefix_ones(wrbyteen)) |-> operand == sel_byte(wrdata, byte_idx(wrbyteen)));

  // Result must be zero-extended operand
  assert property ((wren && is_prefix_ones(wrbyteen)) |-> (result[7:0] == operand) && (result[127:8] == '0));

  // Write effect: next-cycle reg_file[wraddr] equals result
  assert property ((wren && is_prefix_ones(wrbyteen)) |=> reg_file[wraddr] == result);

  // No write when mask is illegal
  assert property ((wren && !is_prefix_ones(wrbyteen)) |=> $stable(reg_file));

  // Read port 1 behavior
  assert property (rd1en |-> rd1data == $past(reg_file[rd1addr]));
  assert property (!rd1en |-> rd1data == 128'b0);

  // Read port 2 behavior
  assert property (rd2en |-> rd2data == $past(reg_file[rd2addr]));
  assert property (!rd2en |-> rd2data == 128'b0);

  // Read-during-write same-address returns old data
  assert property ((rd1en && wren && is_prefix_ones(wrbyteen) && (rd1addr == wraddr)) |-> rd1data == $past(reg_file[rd1addr]));
  assert property ((rd2en && wren && is_prefix_ones(wrbyteen) && (rd2addr == wraddr)) |-> rd2data == $past(reg_file[rd2addr]));

  // Coverage
  cover property (wren && is_prefix_ones(wrbyteen)); // any legal write
  genvar k; generate
    for (k=0; k<16; k++) begin : C_BE
      cover property (wren && wrbyteen == ((16'h1 << (k+1)) - 1));
    end
  endgenerate
  cover property (rd1en && rd2en);
  cover property (wren && rd1en && (wraddr == rd1addr));
  cover property (wren && rd2en && (wraddr == rd2addr));
  cover property (wren && !is_prefix_ones(wrbyteen)); // illegal mask seen
endmodule

bind RegFileWW RegFileWW_sva sva();