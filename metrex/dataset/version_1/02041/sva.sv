// SVA for memory_module
// Bind this module to the DUT: bind memory_module memory_module_sva m_sva(.*);

module memory_module_sva (
  input logic         clk_i,
  input logic         rst_i,
  input logic         we_i,
  input logic         stb_i,
  input logic [2:0]   adr_i,
  input logic [15:0]  dat_i,
  input logic         ack_o,
  input logic [15:0]  dat_o,
  input logic [15:0]  a11, a12, b10, b11, b12
);

  default clocking cb @(posedge clk_i); endclocking

  // Local decode (mirrors DUT)
  logic sel_a11, sel_a12, sel_b10, sel_b11, sel_b12, any_sel;
  assign sel_a11 = (adr_i == 3'b000);
  assign sel_a12 = (adr_i == 3'b001);
  assign sel_b10 = (adr_i == 3'b010);
  assign sel_b11 = (adr_i == 3'b011);
  assign sel_b12 = (adr_i == 3'b100);
  assign any_sel = sel_a11 | sel_a12 | sel_b10 | sel_b11 | sel_b12;

  // Basic protocol/structural
  assert property (cb ack_o == stb_i);
  assert property (cb $onehot0({sel_a11, sel_a12, sel_b10, sel_b11, sel_b12}));
  assert property (cb !$isunknown({ack_o, dat_o}));

  // Reset values held while in reset
  assert property (cb rst_i |-> (a11==16'h00FF && a12==16'h001F &&
                                 b10==16'h007F && b11==16'h0003 &&
                                 b12==16'h00FF));

  // Read mux correctness (always)
  assert property (cb
    dat_o == (sel_a11 ? a11 :
             (sel_a12 ? a12 :
             (sel_b10 ? b10 :
             (sel_b11 ? b11 :
             (sel_b12 ? b12 : 16'h0000)))))
  );

  // No-write => all registers stable next cycle
  assert property (cb disable iff (rst_i)
    !(stb_i && we_i && any_sel) |=> (a11==$past(a11) && a12==$past(a12) &&
                                     b10==$past(b10) && b11==$past(b11) &&
                                     b12==$past(b12))
  );

  // Invalid address write attempt => no register changes
  assert property (cb disable iff (rst_i)
    (stb_i && we_i && !any_sel) |=> (a11==$past(a11) && a12==$past(a12) &&
                                     b10==$past(b10) && b11==$past(b11) &&
                                     b12==$past(b12))
  );

  // Write updates the targeted register on next cycle; others unchanged
  assert property (cb disable iff (rst_i)
    (stb_i && we_i && sel_a11) |=> (a11==$past(dat_i) &&
                                    a12==$past(a12) && b10==$past(b10) &&
                                    b11==$past(b11) && b12==$past(b12))
  );
  assert property (cb disable iff (rst_i)
    (stb_i && we_i && sel_a12) |=> (a12==$past(dat_i) &&
                                    a11==$past(a11) && b10==$past(b10) &&
                                    b11==$past(b11) && b12==$past(b12))
  );
  assert property (cb disable iff (rst_i)
    (stb_i && we_i && sel_b10) |=> (b10==$past(dat_i) &&
                                    a11==$past(a11) && a12==$past(a12) &&
                                    b11==$past(b11) && b12==$past(b12))
  );
  assert property (cb disable iff (rst_i)
    (stb_i && we_i && sel_b11) |=> (b11==$past(dat_i) &&
                                    a11==$past(a11) && a12==$past(a12) &&
                                    b10==$past(b10) && b12==$past(b12))
  );
  assert property (cb disable iff (rst_i)
    (stb_i && we_i && sel_b12) |=> (b12==$past(dat_i) &&
                                    a11==$past(a11) && a12==$past(a12) &&
                                    b10==$past(b10) && b11==$past(b11))
  );

  // Optional: after reset release, each reg holds reset value until written
  assert property (cb
    $fell(rst_i) |-> (a11==16'h00FF throughout (!stb_i || !we_i || !sel_a11)[*0:$])
  );
  assert property (cb
    $fell(rst_i) |-> (a12==16'h001F throughout (!stb_i || !we_i || !sel_a12)[*0:$])
  );
  assert property (cb
    $fell(rst_i) |-> (b10==16'h007F throughout (!stb_i || !we_i || !sel_b10)[*0:$])
  );
  assert property (cb
    $fell(rst_i) |-> (b11==16'h0003 throughout (!stb_i || !we_i || !sel_b11)[*0:$])
  );
  assert property (cb
    $fell(rst_i) |-> (b12==16'h00FF throughout (!stb_i || !we_i || !sel_b12)[*0:$])
  );

  // Coverage
  cover property (cb stb_i && !we_i && sel_a11);
  cover property (cb stb_i && !we_i && sel_a12);
  cover property (cb stb_i && !we_i && sel_b10);
  cover property (cb stb_i && !we_i && sel_b11);
  cover property (cb stb_i && !we_i && sel_b12);
  cover property (cb stb_i && we_i && sel_a11);
  cover property (cb stb_i && we_i && sel_a12);
  cover property (cb stb_i && we_i && sel_b10);
  cover property (cb stb_i && we_i && sel_b11);
  cover property (cb stb_i && we_i && sel_b12);
  cover property (cb stb_i && !any_sel && (dat_o==16'h0000)); // invalid address read
  cover property (cb $rose(stb_i));
  cover property (cb $fell(stb_i));

endmodule

bind memory_module memory_module_sva m_sva (
  .clk_i, .rst_i, .we_i, .stb_i, .adr_i, .dat_i, .ack_o, .dat_o, .a11, .a12, .b10, .b11, .b12
);