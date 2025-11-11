// SVA binders for the provided design

// true_dual_port_ram assertions
module true_dual_port_ram_sva #(parameter ADDR_W=3, DATA_W=4, DEPTH=(1<<ADDR_W))
(
  input clk,
  input read_en,
  input [ADDR_W-1:0] read_addr,
  input [DATA_W-1:0] read_data,
  input write_en,
  input [ADDR_W-1:0] write_addr,
  input [DATA_W-1:0] write_data
);
  logic [DATA_W-1:0] exp_mem [DEPTH];
  logic [DEPTH-1:0]  init;

  initial begin
    init = '0;
    for (int i=0;i<DEPTH;i++) exp_mem[i] = 'x;
  end

  // mirror write behavior (registered write)
  always_ff @(posedge clk) begin
    if (write_en) begin
      exp_mem[write_addr] <= write_data;
      init[write_addr]    <= 1'b1;
    end
  end

  // read behavior (combinational)
  assert property (@(posedge clk) read_en && init[read_addr] |-> ##0 read_data == exp_mem[read_addr]);
  assert property (@(posedge clk) !read_en |-> ##0 read_data == '0);

  // same-cycle read-during-write to same address is write-first
  assert property (@(posedge clk) write_en && read_en && (read_addr==write_addr) |-> ##0 read_data == write_data);

  // read unaffected by write to different address
  assert property (@(posedge clk) write_en && read_en && (read_addr!=write_addr) && init[read_addr] |-> ##0 read_data == exp_mem[read_addr]);

  // sanity: no X on controls/outputs
  assert property (@(posedge clk) !$isunknown({read_en,write_en,read_addr,write_addr,read_data}));

  // coverage
  cover property (@(posedge clk) write_en ##1 read_en && (read_addr==$past(write_addr)));
  cover property (@(posedge clk) write_en && read_en && (read_addr==write_addr));
  for (genvar a=0;a<DEPTH;a++) begin : cov_addr
    cover property (@(posedge clk) write_en && write_addr==a[ADDR_W-1:0]);
    cover property (@(posedge clk) read_en && init[read_addr] && read_addr==a[ADDR_W-1:0]);
  end
endmodule

bind true_dual_port_ram true_dual_port_ram_sva #(.ADDR_W(3),.DATA_W(4)) ram_sva_b
(
  .clk(clk),
  .read_en(read_en),
  .read_addr(read_addr),
  .read_data(read_data),
  .write_en(write_en),
  .write_addr(write_addr),
  .write_data(write_data)
);


// counter assertions
module counter_sva (input clk, input reset, input [3:0] count);
  assert property (@(posedge clk) reset |-> count==4'h0);
  assert property (@(posedge clk) disable iff (reset) count == $past(count)+1);
  assert property (@(posedge clk) !$isunknown({reset,count}));
  cover  property (@(posedge clk) $past(count)==4'hF && count==4'h0);
  cover  property (@(posedge clk) reset ##1 !reset);
endmodule

bind counter counter_sva cnt_sva_b (.clk(clk), .reset(reset), .count(count));


// register_8bit assertions
module register_8bit_sva (input clk, input reset, input [7:0] d, input [7:0] q);
  assert property (@(posedge clk) reset |-> q==8'h34);
  assert property (@(posedge clk) disable iff (reset) q==$past(d));
  assert property (@(posedge clk) !$isunknown({reset,q}));
  cover  property (@(posedge clk) reset ##1 !reset ##1 $changed(d));
endmodule

bind register_8bit register_8bit_sva reg_sva_b (.clk(clk), .reset(reset), .d(d), .q(q));


// arithmetic_logic assertions
module arithmetic_logic_sva (input [3:0] counter_data, input [7:0] register_data, input [7:0] result);
  assert property (result == {4'b0000,counter_data} + register_data);
  assert property (!$isunknown({counter_data,register_data,result}));
  cover  property (({4'b0000,counter_data} + register_data) < register_data); // carry/overflow
endmodule

bind arithmetic_logic arithmetic_logic_sva alu_sva_b (.counter_data(counter_data), .register_data(register_data), .result(result));


// top_module assertions
module top_module_sva (
  input clk,
  input reset,
  input select,
  input [7:0] q,
  input [7:0] register_output,
  input [7:0] arithmetic_output
);
  // registered mux behavior; use reset to bound $past history
  assert property (@(posedge clk) q == $past(select ? register_output : arithmetic_output, 1, reset));
  assert property (@(posedge clk) !$isunknown({select,q}));
  cover  property (@(posedge clk) $rose(select));
  cover  property (@(posedge clk) $fell(select));
endmodule

bind top_module top_module_sva top_sva_b (
  .clk(clk),
  .reset(reset),
  .select(select),
  .q(q),
  .register_output(register_output),
  .arithmetic_output(arithmetic_output)
);