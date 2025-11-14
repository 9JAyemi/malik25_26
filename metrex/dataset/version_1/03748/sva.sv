// SVA for the provided design. Bind these checkers to the DUT.

// Ripple adder checks
bind ripple_adder ripple_adder_sva ra_sva();
module ripple_adder_sva;
  assert property ( !$isunknown({a,b}) |-> {carry_out,sum} == a + b )
    else $error("ripple_adder: {carry,sum} != a+b");
  // Coverage
  cover property ( (a==16'h0000) || (b==16'h0000) );
  cover property ( carry_out );
  cover property ( sum == 16'h0000 );
  cover property ( sum == 16'hFFFF );
endmodule

// Carry-select adder checks (spec: sum must equal a+b; also check internal ripple instances)
bind carry_select_adder carry_select_adder_sva csa_sva();
module carry_select_adder_sva;
  assert property ( !$isunknown({a,b}) |-> sum == a + b )
    else $error("carry_select_adder: sum != a+b (spec mismatch)");
  assert property ( {adder_low.carry_out, adder_low.sum}  == ({1'b0,a[15:0]}   + {1'b0,b[15:0]}) )
    else $error("carry_select_adder: low half ripple mismatch");
  assert property ( {adder_high.carry_out, adder_high.sum} == ({1'b0,a[31:16]} + {1'b0,b[31:16]}) )
    else $error("carry_select_adder: high half ripple mismatch");
  // Coverage
  cover property ( adder_low.carry_out );
  cover property ( adder_high.carry_out );
  cover property ( adder_low.carry_out && adder_high.carry_out );
endmodule

// Decoder checks
bind decoder_mux_16bit decoder_mux_16bit_sva dec_sva();
module decoder_mux_16bit_sva;
  assert property ( upper_byte == in[15:8] ) else $error("decoder: upper_byte mismatch");
  assert property ( lower_byte == in[7:0] ) else $error("decoder: lower_byte mismatch");
  // Coverage
  cover property ( in == 16'h0000 );
  cover property ( in == 16'hFFFF );
endmodule

// Functional module (multiplier) checks
bind functional_module functional_module_sva fun_sva();
module functional_module_sva;
  assert property ( out == (a*b)[7:0] ) else $error("functional_module: out != (a*b)[7:0]");
  // Coverage
  cover property ( (a==8'h00) || (b==8'h00) );
  cover property ( (a*b) > 16'h00FF ); // truncation/overflow
endmodule

// Top-level end-to-end and structural checks
bind top_module top_module_sva top_sva();
module top_module_sva;
  function automatic [7:0] ref_out(input logic [31:0] ai, bi, input logic sel);
    automatic logic [31:0] s;
    automatic logic [7:0] up, lo, prod;
    s    = ai + bi;
    up   = s[15:8];
    lo   = s[7:0];
    prod = (up*lo)[7:0];
    ref_out = sel ? prod : lo;
  endfunction

  // End-to-end spec from inputs
  assert property ( !$isunknown({a,b,select}) |-> out == ref_out(a,b,select) )
    else $error("top_module: end-to-end mismatch");

  // Structural consistency within top
  assert property ( {upper_byte,lower_byte} == (sum[15:0]) ) else $error("top_module: decoder wiring mismatch");
  assert property ( product == (upper_byte*lower_byte)[7:0] ) else $error("top_module: functional_module wiring mismatch");
  assert property ( select |-> out == product ) else $error("top_module: mux select=1 path mismatch");
  assert property ( !select |-> out == lower_byte ) else $error("top_module: mux select=0 path mismatch");
  assert property ( !$isunknown(select) ) else $error("top_module: select is X/Z");

  // Coverage
  cover property ( select==1'b0 );
  cover property ( select==1'b1 );
  cover property ( select && (( ( (a+b)[15:8] * (a+b)[7:0]) ) > 16'h00FF) ); // product truncation on product path
endmodule