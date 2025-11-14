// SVA for decode38/regxb/dso_regw/dso_regr
// Focused, high-quality checks with concise coverage.

// Bindable SVA for regxb: checks async reset, write-enable capture, and hold
module regxb_sva #(parameter bits = 1)
(
  input logic        clk,
  input logic        nrst,
  input logic        en,
  input logic [bits-1:0] din,
  input logic [bits-1:0] regout
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears immediately and holds while low
  a_async_clear_now: assert property (@(negedge nrst) regout == '0);
  a_clear_while_low: assert property (cb !nrst |-> regout == '0);

  // On write enable, capture din next cycle; otherwise hold value
  a_capture_on_en:  assert property (cb disable iff (!nrst) en  |=> regout == $past(din));
  a_hold_on_no_en:  assert property (cb disable iff (!nrst) !en |=> regout == $past(regout));

  // Simple coverage
  c_write:           cover property (cb disable iff (!nrst) en);
  c_hold:            cover property (cb disable iff (!nrst) !en);
endmodule


// Bindable SVA for dso_regw: checks decode, onehot, register update routing, and reset behavior
module dso_regw_sva
(
  input  logic       nrst,
  input  logic       clk,
  input  logic [2:0] addr,
  input  logic [7:0] din,
  input  logic       we,
  input  logic [7:0] sel,
  input  logic [7:0] reg0, reg1, reg2, reg3, reg4, reg5, reg6, reg7
);
  default clocking cb @(posedge clk); endclocking

  // Decode/SEL correctness
  a_sel_match:        assert property (cb sel == (we ? (8'h1 << addr) : 8'h00));
  a_sel_onehot:       assert property (cb we |-> $onehot(sel));
  a_sel_zero_when_no: assert property (cb !we |-> sel == 8'h00);

  // Global reset behavior (all regs clear asynchronously and hold while low)
  a_regs_async_clear: assert property (@(negedge nrst)
                                       {reg7,reg6,reg5,reg4,reg3,reg2,reg1,reg0} == {8{8'h00}});
  a_regs_hold_low:    assert property (cb !nrst |-> {reg7,reg6,reg5,reg4,reg3,reg2,reg1,reg0} == {8{8'h00}});

  // Per-address write routing and non-selected stability
  genvar i;
  generate
    for (i=0; i<8; i++) begin : G_W
      // Selected register updates to previous-cycle din
      a_sel_updates_i:     assert property (cb disable iff (!nrst)
                                 (we && addr==i[2:0]) |=> {reg7,reg6,reg5,reg4,reg3,reg2,reg1,reg0}[8*(7-i)+:8] == $past(din));
      // Non-selected registers hold when a write occurs to some other address
      a_unsel_hold_i:      assert property (cb disable iff (!nrst)
                                 (we && addr!=i[2:0]) |=> $stable({reg7,reg6,reg5,reg4,reg3,reg2,reg1,reg0}[8*(7-i)+:8]));
      // Address coverage
      c_addr_i:            cover  property (cb disable iff (!nrst) we && addr==i[2:0]);
    end
  endgenerate

  // When no write, all regs hold
  a_hold_on_no_we:    assert property (cb disable iff (!nrst)
                                  !we |=> $stable({reg7,reg6,reg5,reg4,reg3,reg2,reg1,reg0}));
endmodule


// Bindable SVA for dso_regr: mux correctness (clockless via immediate assertions)
module dso_regr_imm_sva
(
  input  logic [2:0] addr,
  input  logic [7:0] dout,
  input  logic [7:0] reg0, reg1, reg2, reg3, reg4, reg5, reg6, reg7
);
  // Mux must reflect selected register combinationally
  always @* begin
    assert (dout === (addr==3'h0 ? reg0 :
                      addr==3'h1 ? reg1 :
                      addr==3'h2 ? reg2 :
                      addr==3'h3 ? reg3 :
                      addr==3'h4 ? reg4 :
                      addr==3'h5 ? reg5 :
                      addr==3'h6 ? reg6 : reg7))
      else $error("dso_regr mux mismatch");
  end

  // Simple address coverage
  genvar j;
  generate
    for (j=0; j<8; j++) begin : G_C
      always @* cover (addr==j[2:0]);
    end
  endgenerate
endmodule


// Optional: SVA for decode38 instance via dso_regw signals (sel mirrors decode output)
module decode38_via_regw_sva
(
  input logic       clk,
  input logic       nrst,
  input logic       we,
  input logic [2:0] addr,
  input logic [7:0] sel
);
  default clocking cb @(posedge clk); endclocking

  a_dec_exact:  assert property (cb sel == (we ? (8'h1 << addr) : 8'h00));
  a_dec_1hot:   assert property (cb we |-> $onehot(sel));
  // Decode coverage
  genvar k;
  generate
    for (k=0; k<8; k++) begin : G_DEC_C
      c_dec_k: cover property (cb we && (addr==k[2:0]) && sel[k]);
    end
  endgenerate
endmodule


// Binds
bind regxb    regxb_sva  #(.bits(bits)) regxb_sva_i (.clk(clk), .nrst(nrst), .en(en), .din(din), .regout(regout));
bind dso_regw dso_regw_sva                               dso_regw_sva_i (.nrst(nrst), .clk(clk), .addr(addr), .din(din), .we(we),
                                                                           .sel(sel),
                                                                           .reg0(reg0), .reg1(reg1), .reg2(reg2), .reg3(reg3),
                                                                           .reg4(reg4), .reg5(reg5), .reg6(reg6), .reg7(reg7));
bind dso_regw decode38_via_regw_sva                      decode38_sva_i  (.clk(clk), .nrst(nrst), .we(we), .addr(addr), .sel(sel));
// For dso_regr, no clock is required due to immediate assertions:
bind dso_regr dso_regr_imm_sva                           dso_regr_sva_i  (.addr(addr), .dout(dout),
                                                                           .reg0(reg0), .reg1(reg1), .reg2(reg2), .reg3(reg3),
                                                                           .reg4(reg4), .reg5(reg5), .reg6(reg6), .reg7(reg7));