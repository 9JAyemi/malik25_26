// SVA for Peripheral_clk_generator and clk_generator
// Focused, high-quality checks and coverage

// Bind into Peripheral_clk_generator
module periph_clk_gen_sva (
  input         clk,
  input         rst,
  input  [15:0] d_in,
  input         cs,
  input  [3:0]  addr,
  input         rd,
  input         wr,
  input  [5:0]  s,
  input  [31:0] limit,
  input  [31:0] count,
  input         en,
  input         clk_0,
  input  [15:0] d_out,
  input         done
);

  // rd/wr mutual exclusion when selected
  assert property (@(posedge clk) !(cs && rd && wr))
    else $error("rd and wr both asserted with cs");

  // Decode is one-hot or zero
  assert property (@(negedge clk) $onehot0(s))
    else $error("s decode not onehot0");

  // Address decode correctness (concise sanity)
  assert property (@(negedge clk)
    (cs && wr && (addr==4'h0)) |-> s==6'b000001)
    else $error("addr 0x0 write did not set s[0]");
  assert property (@(negedge clk)
    (cs && wr && (addr==4'h2)) |-> s==6'b000010)
    else $error("addr 0x2 write did not set s[1]");
  assert property (@(negedge clk)
    (cs && wr && (addr==4'h4)) |-> s==6'b000100)
    else $error("addr 0x4 write did not set s[2]");
  assert property (@(negedge clk)
    (cs && rd && (addr==4'h6)) |-> s==6'b001000)
    else $error("addr 0x6 read did not set s[3]");
  assert property (@(negedge clk)
    (cs && rd && (addr==4'h8)) |-> s==6'b010000)
    else $error("addr 0x8 read did not set s[4]");
  // No decode elsewhere
  assert property (@(negedge clk)
    cs && (rd||wr) && !((addr==4'h0 && wr) || (addr==4'h2 && wr) || (addr==4'h4 && wr) ||
                        (addr==4'h6 && rd) || (addr==4'h8 && rd)) |-> s==6'b0)
    else $error("Unexpected s decode for unsupported address");

  // Writes only change targeted regs on negedge
  // limit/count get zero-extended d_in; en takes d_in[0]
  assert property (@(negedge clk) s[0] |-> (limit[15:0]==d_in && limit[31:16]==16'h0))
    else $error("limit write mismatch/upper bits not zero");
  assert property (@(negedge clk) !s[0] |-> $stable(limit))
    else $error("limit changed without write");

  assert property (@(negedge clk) s[1] |-> (count[15:0]==d_in && count[31:16]==16'h0))
    else $error("count write mismatch/upper bits not zero");
  assert property (@(negedge clk) !s[1] |-> $stable(count))
    else $error("count changed without write");

  assert property (@(negedge clk) s[2] |-> (en==d_in[0]))
    else $error("en write mismatch");
  assert property (@(negedge clk) !s[2] |-> $stable(en))
    else $error("en changed without write");

  // Read behavior drives d_out as coded
  assert property (@(negedge clk) s[3] |-> (d_out[0]==done && d_out[15:1]==$past(d_out[15:1])))
    else $error("done read mapping to d_out[0] incorrect");
  assert property (@(negedge clk) s[4] |-> (d_out=={15'b0,clk_0}))
    else $error("clk_0 read mapping to d_out incorrect");
  assert property (@(negedge clk) !(s[3]||s[4]) |-> (d_out==16'h0))
    else $error("d_out not zero when not reading");

  // Coverage: exercise all accesses
  cover property (@(negedge clk) s[0]); // write limit
  cover property (@(negedge clk) s[1]); // write count
  cover property (@(negedge clk) s[2]); // write en
  cover property (@(negedge clk) s[3]); // read done
  cover property (@(negedge clk) s[4]); // read clk_0
  // Back-to-back different writes
  cover property (@(negedge clk) s[0] ##1 s[1]);
endmodule

bind Peripheral_clk_generator periph_clk_gen_sva
  periph_clk_gen_sva_i (
    .clk(clk),
    .rst(rst),
    .d_in(d_in),
    .cs(cs),
    .addr(addr),
    .rd(rd),
    .wr(wr),
    .s(s),
    .limit(limit),
    .count(count),
    .en(en),
    .clk_0(clk_0),
    .d_out(d_out),
    .done(done)
  );

// Bind into clk_generator
module clk_generator_sva (
  input        clk,
  input        rst,
  input [31:0] limit,
  input        en,
  input        clk_0,
  input        done,
  input [31:0] cnt
);
  // Reset behavior
  assert property (@(posedge clk) rst |-> (cnt==0 && clk_0==0 && done==1))
    else $error("Reset behavior incorrect");

  // When disabled, outputs/ctr forced
  assert property (@(posedge clk) disable iff (rst) !en |-> (cnt==0 && clk_0==0 && done==1))
    else $error("Disabled behavior incorrect");

  // While enabled: done reflects compare; count up or wrap+toggle
  assert property (@(posedge clk) disable iff (rst) en |-> (done == (cnt==limit)))
    else $error("done not equal to (cnt==limit) while enabled");

  assert property (@(posedge clk) disable iff (rst)
    (en && (cnt!=limit)) |=> (cnt==$past(cnt)+1 && done==0))
    else $error("Counting step incorrect");

  assert property (@(posedge clk) disable iff (rst)
    (en && (cnt==limit)) |=> (cnt==0 && done==1 && clk_0==$past(clk_0)^1'b1))
    else $error("Wrap/toggle behavior incorrect");

  // clk_0 only toggles on compares (prior cycle)
  assert property (@(posedge clk) disable iff (rst)
    $changed(clk_0) |-> $past(en && (cnt==limit)))
    else $error("clk_0 toggled without compare match while enabled");

  // Coverage: exercise key scenarios
  // Toggle under nonzero limit
  cover property (@(posedge clk) disable iff (rst)
    en && (limit!=0) ##1 (cnt==limit) ##1 (clk_0!=$past(clk_0)));
  // Limit==0 corner (continuous done)
  cover property (@(posedge clk) disable iff (rst)
    en && (limit==0) [*3] ##1 (done==1));
  // Several toggles observed
  cover property (@(posedge clk) disable iff (rst)
    en && (cnt==limit) ##1 (clk_0!=$past(clk_0)) ##[1:100] (en && (cnt==limit)) ##1 (clk_0!=$past(clk_0)));
endmodule

bind clk_generator clk_generator_sva
  clk_generator_sva_i (
    .clk(clk),
    .rst(rst),
    .limit(limit),
    .en(en),
    .clk_0(clk_0),
    .done(done),
    .cnt(cnt)
  );