// SVA for top_module
module top_module_sva();
  // Bound into top_module scope; can see internal regs/wires
  default clocking cb @(posedge clk); endclocking
  default disable iff (async_reset || sync_reset);

  function automatic logic [3:0] bcd_model (input logic [3:0] c);
    case (c)
      4'd0: bcd_model = 4'd0;
      4'd1: bcd_model = 4'd1;
      4'd2: bcd_model = 4'd2;
      4'd3: bcd_model = 4'd3;
      4'd4: bcd_model = 4'd4;
      4'd5: bcd_model = 4'd5;
      4'd6: bcd_model = 4'd6;
      4'd7: bcd_model = 4'd7;
      4'd8: bcd_model = 4'd8;
      4'd9: bcd_model = 4'd9;
      default: bcd_model = 4'd0;
    endcase
  endfunction

  // Asynchronous reset effects (both resets act asynchronously in RTL)
  property p_async_reset_dom; @(posedge async_reset) ##0 (johnson==4'b0001 && count==4'b0000 && q==16'h0000); endproperty
  property p_sync_reset_dom;  @(posedge sync_reset)  ##0 (johnson==4'b0001 && count==4'b0000 && q==16'h0000); endproperty
  assert property(p_async_reset_dom);
  assert property(p_sync_reset_dom);
  // Hold reset values while reset held high
  assert property ( (async_reset || sync_reset) |-> (johnson==4'b0001 && count==4'b0000 && q==16'h0000) );

  // Ring counter behavior
  assert property ( $onehot(johnson) );
  assert property ( johnson == { $past(johnson,1,4'b0001)[2:0], $past(johnson,1,4'b0001)[3] } );

  // Count update gated by johnson[3] (increment when j[3]==0, hold when j[3]==1)
  assert property ( $past(johnson[3],1,1'b0) |-> (count == $past(count,1,4'd0)) );
  assert property ( !$past(johnson[3],1,1'b0) |-> (count == $past(count,1,4'd0) + 4'd1) );

  // BCD decoder correctness
  assert property ( (count <= 4'd9)  -> (bcd == count) );
  assert property ( (count >= 4'd10) -> (bcd == 4'd0) );

  // Enable decode correctness and onehot0
  assert property ( (johnson==4'b0001) -> (ena==3'b100) );
  assert property ( (johnson==4'b0010) -> (ena==3'b010) );
  assert property ( (johnson==4'b0100) -> (ena==3'b001) );
  assert property ( !(johnson inside {4'b0001,4'b0010,4'b0100}) -> (ena==3'b000) );
  assert property ( $onehot0(ena) );

  // q formatting and timing (replicates decoded previous count)
  assert property ( q[15:12]==q[11:8] && q[11:8]==q[7:4] && q[7:4]==q[3:0] );
  assert property ( q == {4{ bcd_model($past(count,1,4'd0)) }} );

  // Functional coverage
  cover property ( johnson==4'b0001 ##1 johnson==4'b0010 ##1 johnson==4'b0100 ##1 johnson==4'b1000 ##1 johnson==4'b0001 );
  cover property ( count==4'd9 ##1 count==4'd10 );
  cover property ( ena==3'b100 ##1 ena==3'b010 ##1 ena==3'b001 ##1 ena==3'b000 ##1 ena==3'b100 );
  cover property ( q[3:0]==4'd0 && $past(count,1,4'd0)==4'd10 );
endmodule

bind top_module top_module_sva sva_top_module();