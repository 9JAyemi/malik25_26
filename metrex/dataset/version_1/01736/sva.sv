// SVA for toy_icache
// Enable by compiling this file with the DUT. Uses bind so DUT code stays unchanged.

`ifdef DUMMY_CACHE

module toy_icache_sva_dummy(
  input logic         clk,
  input logic         reset,
  input logic [31:0]  ic_addr,
  input logic         ic_rq,
  input logic         ic_data_out_valid,
  input logic [31:0]  ic_data_out,
  input logic [31:0]  data_in,
  input logic         data_in_ready,
  input logic         data_rd,
  input logic [31:0]  data_address
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Pass-through timing (1-cycle registered)
  assert property (data_address == $past(ic_addr));
  assert property (data_rd      == $past(ic_rq));
  assert property (ic_data_out_valid == $past(data_in_ready));
  assert property (ic_data_out       == $past(data_in));

  // No X on outputs
  assert property (!$isunknown({ic_data_out_valid, data_rd}));

  // Basic coverage
  cover property ($rose(data_in_ready));
  cover property (data_in_ready && $fell(ic_rq)); // some activity
endmodule

bind toy_icache toy_icache_sva_dummy u_sva_dummy (
  .clk(clk), .reset(reset),
  .ic_addr(ic_addr), .ic_rq(ic_rq),
  .ic_data_out_valid(ic_data_out_valid), .ic_data_out(ic_data_out),
  .data_in(data_in), .data_in_ready(data_in_ready),
  .data_rd(data_rd), .data_address(data_address)
);

`else  // !DUMMY_CACHE

module toy_icache_sva_full
(
  input  logic                     clk,
  input  logic                     reset,

  // Ports
  input  logic [31:0]              ic_addr,
  input  logic                     ic_rq,
  input  logic                     ic_data_out_valid,
  input  logic [31:0]              ic_data_out,

  input  logic [31:0]              data_in,
  input  logic                     data_in_ready,
  input  logic                     data_rd,
  input  logic [31:0]              data_address,

  // Internals
  input  logic [31-`IC_WIDTH_BITS+1:0] ictags [0:`IC_LINES-1],
  input  logic [31:0]                  cacheram [0:(`IC_LINES*`IC_WIDTH)-1],
  input  logic [31-`IC_WIDTH_BITS:0]   addrtag,
  input  logic [31-`IC_WIDTH_BITS+1:0] icnewtag,
  input  logic [2:0]                   ic_state,
  input  logic [31:0]                  ictagsout,
  input  logic [1:0]                   ic_rq_shift
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  localparam int INDEX_HI  = `IC_WIDTH_BITS+`IC_LINES_BITS-1;
  localparam int OFFSET_HI = `IC_WIDTH_BITS-1;

  // State encoding check
  assert property (ic_state inside {3'(0),3'(1),3'(2),3'(3)});

  // Shift register behavior
  assert property (ic_rq_shift == { $past(ic_rq_shift[0]), $past(ic_rq) });

  // IDLE hit -> valid with correct data
  assert property ((ic_state==3'(0)) && ic_rq_shift[1] &&
                   (ictagsout == {1'b1, addrtag})
                   |-> ic_data_out_valid && (ic_data_out == cacheram[ic_addr[INDEX_HI:0]]));

  // IDLE no request -> no valid
  assert property ((ic_state==3'(0)) && !ic_rq_shift[1] |-> !ic_data_out_valid);

  // IDLE miss -> FILL_START -> FILL_STEP -> FILL, with proper init
  assert property ((ic_state==3'(0)) && ic_rq_shift[1] &&
                   (ictagsout != {1'b1, addrtag})
                   |=> (ic_state==3'(3) && data_address == { $past(ic_addr)[31:`IC_WIDTH_BITS], `IC_WIDTH_ZERO } &&
                        data_rd==0 && icnewtag == {1'b1, $past(addrtag)})
                   |=> (ic_state==3'(2) && data_rd==1 && !ic_data_out_valid)
                   |=> (ic_state==3'(1)));

  // FILL_STEP -> request drive
  assert property ((ic_state==3'(2)) |-> data_rd==1 && !ic_data_out_valid);

  // While filling and ready, we stop driving read
  assert property ((ic_state==3'(1) && data_in_ready) |-> data_rd==0);

  // FILL progress when not last beat
  assert property ((ic_state==3'(1) && data_in_ready &&
                   (data_address[OFFSET_HI:0] != `IC_WIDTH_ONES))
                   |=> (ic_state==3'(2) && data_address == $past(data_address)+1));

  // FILL completion on last beat: tag update and return to IDLE
  assert property ((ic_state==3'(1) && data_in_ready &&
                   (data_address[OFFSET_HI:0] == `IC_WIDTH_ONES))
                   |=> (ic_state==3'(0) &&
                        ictags[$past(data_address)[`IC_LINES_BITS+`IC_WIDTH_BITS-1:`IC_WIDTH_BITS]] == $past(icnewtag)));

  // Forward-hit during fill when data beats arrive
  assert property ((ic_state==3'(1) && data_in_ready && ic_rq && (data_address == ic_addr))
                   |-> (ic_data_out_valid && ic_data_out == data_in));

  // Fast-forward hit from already written part (no new data yet)
  assert property ((ic_state==3'(1) && !data_in_ready && ic_rq &&
                   (data_address[31:`IC_WIDTH_BITS] == ic_addr[31:`IC_WIDTH_BITS]) &&
                   (ic_addr[OFFSET_HI:0] < data_address[OFFSET_HI:0]))
                   |-> (ic_data_out_valid && ic_data_out == cacheram[ic_addr[INDEX_HI:0]]));

  // Conflict on same index with different tag while waiting -> abort fill, invalidate line
  assert property ((ic_state==3'(1) && !data_in_ready && ic_rq &&
                   (data_address[`IC_LINES_BITS+`IC_WIDTH_BITS-1:`IC_WIDTH_BITS] ==
                    ic_addr[`IC_LINES_BITS+`IC_WIDTH_BITS-1:`IC_WIDTH_BITS]) &&
                   !(data_address[31:`IC_WIDTH_BITS] == ic_addr[31:`IC_WIDTH_BITS]))
                   |=> (ic_state==3'(0) && !ic_data_out_valid &&
                        ictags[ic_addr[`IC_WIDTH_BITS+`IC_LINES_BITS-1:`IC_WIDTH_BITS]]==0));

  // Valid can only be asserted in the three legal cases
  assert property (ic_data_out_valid |->
                   ((ic_state==3'(0) && ic_rq_shift[1] && (ictagsout == {1'b1, addrtag})) ||
                    (ic_state==3'(1) && data_in_ready && ic_rq && (data_address == ic_addr)) ||
                    (ic_state==3'(1) && !data_in_ready && ic_rq &&
                     (data_address[31:`IC_WIDTH_BITS] == ic_addr[31:`IC_WIDTH_BITS]) &&
                     (ic_addr[OFFSET_HI:0] < data_address[OFFSET_HI:0]))));

  // Outputs should be known
  assert property (!$isunknown({ic_data_out_valid, data_rd}));

  // Coverage
  cover property ((ic_state==3'(0)) && ic_rq_shift[1] && (ictagsout == {1'b1, addrtag})); // IDLE hit
  cover property ((ic_state==3'(0)) && ic_rq_shift[1] && (ictagsout != {1'b1, addrtag}))
                 ##1 (ic_state==3'(3)) ##1 (ic_state==3'(2))
                 ##[1:$] (ic_state==3'(1) && data_in_ready && (data_address[OFFSET_HI:0]==`IC_WIDTH_ONES))
                 ##1 (ic_state==3'(0)); // miss -> full line fill
  cover property ((ic_state==3'(1) && data_in_ready && ic_rq && (data_address == ic_addr))); // FHIT
  cover property ((ic_state==3'(1) && !data_in_ready && ic_rq &&
                   (data_address[31:`IC_WIDTH_BITS] == ic_addr[31:`IC_WIDTH_BITS]) &&
                   (ic_addr[OFFSET_HI:0] < data_address[OFFSET_HI:0]))); // FFHIT
  cover property ((ic_state==3'(1) && !data_in_ready && ic_rq &&
                   (data_address[`IC_LINES_BITS+`IC_WIDTH_BITS-1:`IC_WIDTH_BITS] ==
                    ic_addr[`IC_LINES_BITS+`IC_WIDTH_BITS-1:`IC_WIDTH_BITS]) &&
                   !(data_address[31:`IC_WIDTH_BITS] == ic_addr[31:`IC_WIDTH_BITS]))); // conflict abort
endmodule

bind toy_icache toy_icache_sva_full u_sva_full (
  .clk(clk), .reset(reset),
  .ic_addr(ic_addr), .ic_rq(ic_rq),
  .ic_data_out_valid(ic_data_out_valid), .ic_data_out(ic_data_out),
  .data_in(data_in), .data_in_ready(data_in_ready),
  .data_rd(data_rd), .data_address(data_address),

  .ictags(ictags), .cacheram(cacheram),
  .addrtag(addrtag), .icnewtag(icnewtag),
  .ic_state(ic_state), .ictagsout(ictagsout),
  .ic_rq_shift(ic_rq_shift)
);

`endif  // DUMMY_CACHE