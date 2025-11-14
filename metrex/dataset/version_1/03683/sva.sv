// SVA for my_module. Bind this to the DUT instance.
// Focused, high-signal-coverage checks + concise functional coverage.

module my_module_sva #(parameter string output_clock = "none")
(
  input  logic clk,
  input  logic aclr,
  input  logic ena,
  input  logic dataa,
  input  logic dataout,
  input  logic [1:0] state
);

  localparam bit HAS_OC = (output_clock != "none");

  default clocking cb @(posedge clk); endclocking
  default disable iff (!aclr);

  // Asynchronous clear must immediately take effect
  assert property (@(negedge aclr) ##0 (state==2'b00 && dataout==1'b0));
  // While aclr is low, registers are held in reset
  assert property ( !aclr |-> (state==2'b00 && dataout==1'b0) );

  // Legal state transitions
  assert property ( (state==2'b00 &&  ena) |=> state==2'b01 );
  assert property ( (state==2'b00 && !ena) |=> state==2'b00 );

  generate
    if (HAS_OC) begin
      assert property ( state==2'b01 |=> state==2'b10 );
      assert property ( state==2'b10 |=> state==2'b11 );
    end
    else begin
      assert property ( state==2'b01 |=> state==2'b00 );
      // 10/11 unreachable when HAS_OC==0
      assert property ( state!=2'b10 && state!=2'b11 );
    end
  endgenerate

  assert property ( state==2'b11 |=> state==2'b00 );

  // Output behavior per state
  assert property ( (state==2'b00 &&  ena) |=> dataout==$past(dataa) );
  assert property ( (state==2'b00 && !ena) |=> dataout==1'b0 );
  assert property ( state==2'b01 |=> dataout==$past(dataout) );

  generate
    if (HAS_OC) begin
      assert property ( state==2'b10 |=> dataout==$past(dataa) );
    end
  endgenerate

  assert property ( state==2'b11 |=> dataout==1'b0 );

  // dataout only changes on clk posedge or aclr negedge
  assert property (@(posedge dataout) ($rose(clk) || $fell(aclr) || !aclr));
  assert property (@(negedge dataout) ($rose(clk) || $fell(aclr) || !aclr));

  // Concise functional coverage
  cover property (@(negedge aclr) 1); // reset seen

  cover property ( (state==2'b00 && !ena) ##1 state==2'b00 ); // idle self-loop
  cover property ( (state==2'b00 &&  ena) ##1 state==2'b01 ); // kick off

  generate
    if (HAS_OC) begin
      cover property ( (state==2'b00 && ena)
                       ##1 state==2'b01 ##1 state==2'b10
                       ##1 state==2'b11 ##1 state==2'b00 );
      cover property ( (state==2'b10 && dataa) ##1 dataout ); // capture '1'
      cover property ( (state==2'b10 && !dataa) ##1 !dataout ); // capture '0'
    end
    else begin
      cover property ( (state==2'b00 && ena) ##1 state==2'b01 ##1 state==2'b00 );
    end
  endgenerate

endmodule

// Bind to DUT (assumes identical parameter value propagates)
bind my_module my_module_sva #(.output_clock(output_clock))
  my_module_sva_b ( .clk(clk), .aclr(aclr), .ena(ena),
                    .dataa(dataa), .dataout(dataout), .state(state) );