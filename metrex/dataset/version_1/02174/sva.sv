// SVA for module key
module key_sva(
  input  logic        clk,
  input  logic        reset_n,
  input  logic        chipselect,
  input  logic        write_n,
  input  logic [1:0]  address,
  input  logic [31:0] writedata,
  input  logic        in_port,
  input  logic        irq,
  input  logic [31:0] readdata,
  input  logic [31:0] read_mux_out,
  input  logic [31:0] readdata_reg,
  input  logic        irq_mask,
  input  logic        clk_en,
  input  logic [31:0] mem0,
  input  logic [31:0] mem1,
  input  logic [31:0] mem2,
  input  logic [31:0] mem3
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Simple combinational/constant checks
  ap_clk_en_const:   assert property (clk_en == 1'b1 && $stable(clk_en));
  ap_irq_comb:       assert property (irq == (in_port & irq_mask));
  ap_readdata_wire:  assert property (readdata == readdata_reg);

  // Async reset values observed on clock
  ap_reset_vals: assert property (!reset_n |-> (readdata_reg==32'h0 && read_mux_out==32'h0 && irq_mask==1'b0 &&
                                                mem0==32'h0 && mem1==32'h0 && mem2==32'h0 && mem3==32'h0));

  // Pipeline: readdata_reg <= $past(read_mux_out)
  ap_readdata_pipe: assert property (readdata_reg == $past(read_mux_out));

  // Read mux mapping (1-cycle latency from address to read_mux_out)
  ap_read_mux_map: assert property (
    read_mux_out ==
      ($past(address)==2'b00 ? $past(mem0) :
       $past(address)==2'b01 ? $past(mem1) :
       $past(address)==2'b10 ? {31'b0,$past(irq_mask)} :
                               $past(mem3))
  );

  // Memory writes (write_n active-low) and stability otherwise
  ap_mem_wr0: assert property ($past(chipselect && ~write_n && (address==2'b00)) |-> mem0 == $past(writedata));
  ap_mem_wr1: assert property ($past(chipselect && ~write_n && (address==2'b01)) |-> mem1 == $past(writedata));
  ap_mem_wr2: assert property ($past(chipselect && ~write_n && (address==2'b10)) |-> mem2 == $past(writedata));
  ap_mem_wr3: assert property ($past(chipselect && ~write_n && (address==2'b11)) |-> mem3 == $past(writedata));

  ap_mem_stable0: assert property (!$past(chipselect && ~write_n && (address==2'b00)) |-> $stable(mem0));
  ap_mem_stable1: assert property (!$past(chipselect && ~write_n && (address==2'b01)) |-> $stable(mem1));
  ap_mem_stable2: assert property (!$past(chipselect && ~write_n && (address==2'b10)) |-> $stable(mem2));
  ap_mem_stable3: assert property (!$past(chipselect && ~write_n && (address==2'b11)) |-> $stable(mem3));

  // irq_mask update behavior (note: updates when write_n==1 and addr==2)
  ap_irqmask_wr:    assert property ($past(chipselect && write_n && (address==2'b10)) |-> irq_mask == $past(writedata[0]));
  ap_irqmask_hold:  assert property (!$past(chipselect && write_n && (address==2'b10)) |-> $stable(irq_mask));

  // Coverage
  cv_wr0: cover property (chipselect && ~write_n && address==2'b00);
  cv_wr1: cover property (chipselect && ~write_n && address==2'b01);
  cv_wr2: cover property (chipselect && ~write_n && address==2'b10);
  cv_wr3: cover property (chipselect && ~write_n && address==2'b11);

  cv_irqmask0: cover property (chipselect && write_n && address==2'b10 && writedata[0]==1'b0);
  cv_irqmask1: cover property (chipselect && write_n && address==2'b10 && writedata[0]==1'b1);

  // Read latency coverage: address sample -> 2 cycles -> readdata
  cv_rd0: cover property (address==2'b00 ##2 (readdata == $past(mem0,2)));
  cv_rd1: cover property (address==2'b01 ##2 (readdata == $past(mem1,2)));
  cv_rd2: cover property (address==2'b10 ##2 (readdata == {31'b0,$past(irq_mask,2)}));
  cv_rd3: cover property (address==2'b11 ##2 (readdata == $past(mem3,2)));

  // IRQ behavior coverage
  cv_irq_hi: cover property (irq_mask && in_port && irq);
  cv_irq_drop_on_in: cover property (irq_mask && !in_port ##1 !irq);
  cv_irq_drop_on_mask: cover property (in_port && !irq_mask ##1 !irq);

endmodule

bind key key_sva u_key_sva(
  .clk(clk),
  .reset_n(reset_n),
  .chipselect(chipselect),
  .write_n(write_n),
  .address(address),
  .writedata(writedata),
  .in_port(in_port),
  .irq(irq),
  .readdata(readdata),
  .read_mux_out(read_mux_out),
  .readdata_reg(readdata_reg),
  .irq_mask(irq_mask),
  .clk_en(clk_en),
  .mem0(mem[0]),
  .mem1(mem[1]),
  .mem2(mem[2]),
  .mem3(mem[3])
);