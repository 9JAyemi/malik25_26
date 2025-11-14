// SVA for blk_mem_gen_1blk_mem_gen_prim_wrapper
// Concise checks + functional scoreboard, with key coverage

module blk_mem_gen_1blk_mem_gen_prim_wrapper_sva #(parameter WIDTH=32, DEPTH=1024)
(
  input  logic [WIDTH-1:0] addra,
  input  logic [WIDTH-1:0] addrb,
  input  logic             clka,
  input  logic             clkb,
  input  logic [WIDTH-1:0] dina,
  input  logic [WIDTH-1:0] doutb,
  input  logic             enb,
  input  logic             wea
);

  // Golden shadow memory (simulation-only)
  logic [WIDTH-1:0] mem_ref [0:DEPTH-1];
  initial begin
    for (int i=0;i<DEPTH;i++) mem_ref[i] = '0;
  end

  // Write modeling + checks
  always @(posedge clka) begin
    if (enb) begin
      assert (!$isunknown({enb, addra, dina})) else
        $error("SVA: Write has X/Z: enb=%b addra=%h dina=%h", enb, addra, dina);
      assert (addra < DEPTH) else
        $error("SVA: Write address out of range: %0d (DEPTH=%0d)", addra, DEPTH);
      mem_ref[addra] <= dina;
    end
  end

  // Read address valid when used
  property p_read_addr_in_range;
    @(posedge clkb) wea |-> (addrb < DEPTH);
  endproperty
  assert property (p_read_addr_in_range) else
    $error("SVA: Read address out of range: %0d (DEPTH=%0d)", addrb, DEPTH);

  // No X/Z on read-side controls when used
  property p_read_ctrl_known;
    @(posedge clkb) wea |-> !$isunknown({wea, addrb});
  endproperty
  assert property (p_read_ctrl_known) else
    $error("SVA: Read control/address has X/Z: wea=%b addrb=%h", wea, addrb);

  // Data correctness: doutb updates to model value on read (sample after NBA with ##0)
  property p_read_data_matches;
    @(posedge clkb) (wea && (addrb < DEPTH)) |-> ##0 (doutb === mem_ref[addrb]);
  endproperty
  assert property (p_read_data_matches) else
    $error("SVA: Read data mismatch at addr=%0d exp=%0h got=%0h", addrb, mem_ref[addrb], doutb);

  // Output must not change on clkb when read not enabled
  property p_doutb_stable_no_read;
    @(posedge clkb) !wea |-> ##0 $stable(doutb);
  endproperty
  assert property (p_doutb_stable_no_read) else
    $error("SVA: doutb changed without read enable");

  // Basic functional coverage
  cover property (@(posedge clka) enb);
  cover property (@(posedge clkb) wea);
  cover property (@(posedge clka) enb && (addra == DEPTH-1));
  cover property (@(posedge clkb) wea && (addrb == DEPTH-1));

  // Write-then-read same address/data coverage
  logic [WIDTH-1:0] last_wr_addr, last_wr_data;
  logic             last_wr_vld;
  always @(posedge clka) if (enb && (addra < DEPTH) && !$isunknown({addra,dina})) begin
    last_wr_addr <= addra;
    last_wr_data <= dina;
    last_wr_vld  <= 1'b1;
  end
  cover property (@(posedge clkb) last_wr_vld && wea && (addrb == last_wr_addr) ##0 (doutb === last_wr_data));

endmodule

bind blk_mem_gen_1blk_mem_gen_prim_wrapper
  blk_mem_gen_1blk_mem_gen_prim_wrapper_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH))
  blk_mem_gen_1blk_mem_gen_prim_wrapper_sva_i (.*);