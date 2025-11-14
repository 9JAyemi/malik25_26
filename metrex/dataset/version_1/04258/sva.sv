// Bindable SVA for top_module
module top_module_sva;

  // Access DUT signals via bind (inside instance scope)
  // clk, data_in, out, serial_data, parity_bits

  default clocking cb @(posedge clk); endclocking

  // Past-valid tracking (no reset in DUT)
  logic past1, past2, past3;
  initial begin past1=0; past2=0; past3=0; end
  always @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
    past3 <= past2;
  end

  // X/unknown checks
  assert property ( !$isunknown(clk) );
  assert property ( past1 |-> !$isunknown({data_in, serial_data, parity_bits, out}) );

  // Helper parity functions (match DUT)
  function automatic bit p0(input logic [7:0] s); return s[0]^s[1]^s[3]^s[4]^s[6]; endfunction
  function automatic bit p1(input logic [7:0] s); return s[0]^s[2]^s[3]^s[5]^s[6]; endfunction
  function automatic bit p2(input logic [7:0] s); return s[1]^s[2]^s[3]^s[7]; endfunction
  function automatic bit p3(input logic [7:0] s); return s[4]^s[5]^s[6]^s[7]; endfunction

  // Stage 1: serial_data registers data_in
  assert property ( past1 |-> serial_data == $past(data_in) );

  // Stage 2: parity_bits computed from previous serial_data
  assert property ( past2 |-> parity_bits[0] == p0($past(serial_data)) );
  assert property ( past2 |-> parity_bits[1] == p1($past(serial_data)) );
  assert property ( past2 |-> parity_bits[2] == p2($past(serial_data)) );
  assert property ( past2 |-> parity_bits[3] == p3($past(serial_data)) );

  // Stage 3: out maps previous parity_bits/serial_data
  assert property ( past2 |-> out[0] == $past(parity_bits[0]) );
  assert property ( past2 |-> out[1] == $past(parity_bits[1]) );
  assert property ( past2 |-> out[3] == $past(parity_bits[2]) );
  assert property ( past2 |-> out[7] == $past(parity_bits[3]) );
  assert property ( past2 |-> out[2] == $past(serial_data[0]) );
  assert property ( past2 |-> out[4] == $past(serial_data[1]) );
  assert property ( past2 |-> out[5] == $past(serial_data[2]) );
  assert property ( past2 |-> out[6] == $past(serial_data[3]) );
  assert property ( past2 |-> out[8] == $past(serial_data[4]) );

  // End-to-end checks (data_in to out)
  assert property ( past3 |-> out[2] == $past(data_in[0],2) );
  assert property ( past3 |-> out[4] == $past(data_in[1],2) );
  assert property ( past3 |-> out[5] == $past(data_in[2],2) );
  assert property ( past3 |-> out[6] == $past(data_in[3],2) );
  assert property ( past3 |-> out[8] == $past(data_in[4],2) );
  assert property ( past3 |-> out[0] == p0($past(data_in,3)) );
  assert property ( past3 |-> out[1] == p1($past(data_in,3)) );
  assert property ( past3 |-> out[3] == p2($past(data_in,3)) );
  assert property ( past3 |-> out[7] == p3($past(data_in,3)) );

  // Functional coverage
  genvar i;
  generate
    for (i=0;i<8;i++) begin : cov_in_bits
      cover property ( past1 && $rose(data_in[i]) );
      cover property ( past1 && $fell(data_in[i]) );
    end
  endgenerate
  cover property ( past3 && $changed(out) );
  cover property ( past3 && (data_in==8'h00) ##1 (data_in==8'hFF) ##1 (data_in==8'hA5) ##1 (data_in==8'h3C) );

endmodule

bind top_module top_module_sva sva_inst();