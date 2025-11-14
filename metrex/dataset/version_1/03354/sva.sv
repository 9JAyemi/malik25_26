// SVA checker + bind for input_fifo_blk_mem_gen_generic_cstr
// Focused, high-signal-coverage, concise

module input_fifo_blk_mem_gen_generic_cstr_sva
  #(parameter int WIDTH = 8,
    parameter int DEPTH = 256,
    parameter int ADDR_WIDTH = $clog2(DEPTH))
(
  input  logic                    clk,
  input  logic                    srst,
  input  logic                    WEA,
  input  logic                    tmp_ram_rd_en,
  input  logic [WIDTH-1:0]        D,
  input  logic [WIDTH-1:0]        Q,
  input  logic [ADDR_WIDTH-1:0]   head,
  input  logic [ADDR_WIDTH-1:0]   tail,
  input  logic [9:0]              gc0_count_d1_reg,
  input  logic [WIDTH-1:0]        mem [0:DEPTH-1]
);

  default clocking cb @(posedge clk); endclocking

  // Local convenience
  logic wr_ok, rd_ok, empty, full;
  assign empty = (gc0_count_d1_reg == 0);
  assign full  = (gc0_count_d1_reg == DEPTH);
  assign wr_ok = WEA && ((head != tail) || empty);   // same as DUT
  assign rd_ok = tmp_ram_rd_en && (head != tail);    // same as DUT

  // Lightweight reference model for ordering and count
  logic [WIDTH-1:0] model_q[$];
  logic [WIDTH-1:0] exp_q;
  logic             rd_fire_d;

  always_ff @(posedge clk) begin
    if (srst) begin
      model_q.delete();
      exp_q     <= '0;
      rd_fire_d <= 1'b0;
    end else begin
      if (wr_ok) model_q.push_back(D);
      if (rd_ok) begin
        // Should never read when empty due to rd_ok gating
        exp_q <= model_q[0];
        model_q.pop_front();
        rd_fire_d <= 1'b1;
      end else begin
        rd_fire_d <= 1'b0;
      end
    end
  end

  // Reset behavior
  assert property (srst |=> head==0 && tail==0 && gc0_count_d1_reg==0);

  // Fundamental bounds
  assert property (disable iff (srst) gc0_count_d1_reg <= DEPTH);
  assert property (head < DEPTH);
  assert property (tail < DEPTH);

  // Head/Tail increment rules
  assert property (disable iff (srst) wr_ok |=> head == $past(head)+1);
  assert property (disable iff (srst) !wr_ok |=> head == $past(head));
  assert property (disable iff (srst) rd_ok |=> tail == $past(tail)+1);
  assert property (disable iff (srst) !rd_ok |=> tail == $past(tail));

  // Counter update rules
  assert property (disable iff (srst) ( wr_ok && !rd_ok) |=> gc0_count_d1_reg == $past(gc0_count_d1_reg)+1);
  assert property (disable iff (srst) (!wr_ok &&  rd_ok) |=> gc0_count_d1_reg == $past(gc0_count_d1_reg)-1);
  assert property (disable iff (srst) ( wr_ok &&  rd_ok) |=> gc0_count_d1_reg == $past(gc0_count_d1_reg));
  assert property (disable iff (srst) (!wr_ok && !rd_ok) |=> gc0_count_d1_reg == $past(gc0_count_d1_reg));

  // Count vs pointer relationship (circular FIFO invariant)
  assert property (disable iff (srst) (gc0_count_d1_reg==0)      |-> (head==tail));
  assert property (disable iff (srst) (gc0_count_d1_reg==DEPTH)  |-> (head==tail));
  assert property (disable iff (srst) (gc0_count_d1_reg>0 && gc0_count_d1_reg<DEPTH) |-> (head!=tail));

  // Blocked operations
  assert property (disable iff (srst) (tmp_ram_rd_en && empty) |=> $stable(tail) && $stable(gc0_count_d1_reg) && $stable(Q));
  assert property (disable iff (srst) (WEA && full && (head==tail)) |=> $stable(head) && $stable(gc0_count_d1_reg));

  // Data integrity:
  // 1) Memory write must store D at the written address (catch: DUT currently stores WEA)
  assert property (disable iff (srst) wr_ok |=> mem[$past(head)] == $past(D));

  // 2) Read data order vs reference model (catch: DUT uses mem[tail-1])
  assert property (disable iff (srst) rd_fire_d |-> Q == exp_q);

  // 3) Optional direct implementation expectation (intended design): Q after read = mem at old tail
  assert property (disable iff (srst) $past(rd_ok) |-> Q == $past(mem[$past(tail)]));

  // Model vs count consistency
  assert property (disable iff (srst) gc0_count_d1_reg == model_q.size());

  // Targeted coverage
  cover property (disable iff (srst) wr_ok);                    // any write
  cover property (disable iff (srst) rd_ok);                    // any read
  cover property (disable iff (srst) wr_ok && rd_ok);           // simultaneous wr+rd
  cover property (disable iff (srst) (gc0_count_d1_reg==DEPTH)); // reached full
  cover property (disable iff (srst) (gc0_count_d1_reg==0));     // empty
  cover property (disable iff (srst) wr_ok && ($past(head)==DEPTH-1) ##1 (head==0)); // head wrap
  cover property (disable iff (srst) rd_ok && ($past(tail)==DEPTH-1) ##1 (tail==0)); // tail wrap
  cover property (disable iff (srst) (tmp_ram_rd_en && empty));  // underflow attempt
  cover property (disable iff (srst) (WEA && full));             // overflow attempt

endmodule

bind input_fifo_blk_mem_gen_generic_cstr
  input_fifo_blk_mem_gen_generic_cstr_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH), .ADDR_WIDTH(ADDR_WIDTH))
  i_input_fifo_blk_mem_gen_generic_cstr_sva
  (
    .clk(clk),
    .srst(srst),
    .WEA(WEA),
    .tmp_ram_rd_en(tmp_ram_rd_en),
    .D(D),
    .Q(Q),
    .head(head),
    .tail(tail),
    .gc0_count_d1_reg(gc0_count_d1_reg),
    .mem(mem)
  );