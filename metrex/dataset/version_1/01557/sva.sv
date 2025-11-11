// SVA for mig_7series_v1_8_ddr_of_pre_fifo
// Focused, high-quality checks and useful coverage

module mig_7series_v1_8_ddr_of_pre_fifo_sva #(
  parameter int DEPTH = 4,
  parameter int WIDTH = 32
)(
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  full_in,
  input  logic                  wr_en_in,
  input  logic [WIDTH-1:0]      d_in,
  input  logic                  wr_en_out,
  input  logic [WIDTH-1:0]      d_out,
  input  logic                  afull,

  // Internals
  input  logic [2:0]            my_empty,
  input  logic [2:0]            my_full,
  input  logic [$clog2(DEPTH+(DEPTH==1))-1:0] rd_ptr, // safe width if DEPTH=1
  input  logic [$clog2(DEPTH+(DEPTH==1))-1:0] wr_ptr,
  input  logic [$clog2(DEPTH+1)-1:0]          entry_cnt,
  input  logic [$clog2(DEPTH+(DEPTH==1))-1:0] nxt_rd_ptr,
  input  logic [$clog2(DEPTH+(DEPTH==1))-1:0] nxt_wr_ptr,
  input  logic [WIDTH-1:0]      mem_out,
  input  logic                  wr_en
);

  // Recompute localparams used in DUT
  localparam int PTR_BITS = (DEPTH == 2) ? 1 :
                            ((DEPTH == 3) || (DEPTH == 4)) ? 2 :
                            (((DEPTH == 5) || (DEPTH == 6) ||
                              (DEPTH == 7) || (DEPTH == 8)) ? 3 :
                              (DEPTH == 9) ? 4 : 0);
  localparam int ALMOST_FULL_VALUE = DEPTH - 5;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Handy conditions (match DUT)
  wire cond_rd     = (!my_empty[2] && !full_in);
  wire cond_wrptr  = (wr_en_in && ((!my_empty[2] && !full_in) || (!my_full[1] && full_in)));
  wire cond_wr     = (wr_en_in && ((!my_empty[2] && !full_in) || (!my_full[2] && full_in)));
  wire inc_cnt     = (wr_en_in &&  full_in && !my_full[1]);
  wire dec_cnt     = (!wr_en_in && !full_in && !my_empty[2]);

  // Reset values (checked in-cycle when rst is 1)
  assert property (@(posedge clk) rst |-> (rd_ptr=='0 && wr_ptr=='0 &&
                                           my_empty==3'b111 && my_full==3'b000 &&
                                           entry_cnt=='0));

  // Range/sanity
  assert property (rd_ptr < DEPTH);
  assert property (wr_ptr < DEPTH);
  assert property (entry_cnt <= DEPTH);
  assert property (!(my_empty[2] && my_full[2])); // not both empty and full
  assert property (my_empty == {3{my_empty[0]}}); // bits track together
  assert property (my_full  == {3{my_full[0]}});

  // Functional equivalence checks
  assert property (wr_en_out == (!full_in && (!my_empty[1] || wr_en_in)));
  assert property (wr_en     == cond_wr);
  assert property (d_out     == (my_empty[0] ? d_in : mem_out));
  assert property (afull     == (entry_cnt >= ALMOST_FULL_VALUE));

  // Pointer update correctness
  assert property (cond_rd    |-> ##1 (rd_ptr == $past(nxt_rd_ptr)));
  assert property (!cond_rd   |-> ##1 (rd_ptr == $past(rd_ptr)));

  assert property (cond_wrptr |-> ##1 (wr_ptr == $past(nxt_wr_ptr)));
  assert property (!cond_wrptr|-> ##1 (wr_ptr == $past(wr_ptr)));

  // Entry count update and safety
  assert property (inc_cnt    |-> ##1 (entry_cnt == $past(entry_cnt)+1));
  assert property (dec_cnt    |-> ##1 (entry_cnt == $past(entry_cnt)-1));
  assert property (!(inc_cnt && dec_cnt)); // mutually exclusive by design

  // No underflow on decrement
  assert property (dec_cnt |-> ($past(entry_cnt) > 0));

  // Basic X-propagation checks on outputs
  assert property (!$isunknown({wr_en_out, afull})); 
  assert property (!$isunknown(d_out)));

  // Useful coverage
  cover property ($fell(rst)); // reset release
  cover property (my_empty==3'b111 ##1 my_empty==3'b000 ##1 my_empty==3'b111); // empty->nonempty->empty
  cover property (my_full==3'b000 ##1 my_full==3'b111 ##1 my_full==3'b000);   // not-full->full->not-full
  cover property (!afull ##[1:$] afull ##[1:$] !afull);                       // afull crossing

  // Bypass vs memory path
  cover property (my_empty[0] && (d_out==d_in));
  cover property (!my_empty[0] && !full_in && cond_rd); // memory read path

  // Simultaneous read/write when allowed
  cover property (wr_en_in && !my_empty[2] && !full_in);

  // Pointer wrap-around
  if (DEPTH > 1) begin
    cover property ((wr_ptr == DEPTH-1) && cond_wrptr ##1 (wr_ptr == 0));
    cover property ((rd_ptr == DEPTH-1) && cond_rd    ##1 (rd_ptr == 0));
  end

endmodule

// Bind into the DUT; connect to internals explicitly
bind mig_7series_v1_8_ddr_of_pre_fifo
  mig_7series_v1_8_ddr_of_pre_fifo_sva #(.DEPTH(DEPTH), .WIDTH(WIDTH)) u_sva (
    .clk(clk),
    .rst(rst),
    .full_in(full_in),
    .wr_en_in(wr_en_in),
    .d_in(d_in),
    .wr_en_out(wr_en_out),
    .d_out(d_out),
    .afull(afull),

    .my_empty(my_empty),
    .my_full(my_full),
    .rd_ptr(rd_ptr),
    .wr_ptr(wr_ptr),
    .entry_cnt(entry_cnt),
    .nxt_rd_ptr(nxt_rd_ptr),
    .nxt_wr_ptr(nxt_wr_ptr),
    .mem_out(mem_out),
    .wr_en(wr_en)
  );