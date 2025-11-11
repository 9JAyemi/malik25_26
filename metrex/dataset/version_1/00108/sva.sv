// Bindable SVA checker for reverse_mux_and
module reverse_mux_and_sva (
  input  logic [7:0] in,
  input  logic [3:0] in0, in1, in2, in3,
  input  logic [1:0] sel,
  input  logic [3:0] out,

  // Internal DUT nets (bound hierarchically)
  input  logic [7:0] reversed_in,
  input  logic [3:0] selected_input,
  input  logic [3:0] and_output
);

  // Helper
  function automatic logic [3:0] mux4 (input logic [1:0] s,
                                       input logic [3:0] a0,a1,a2,a3);
    case (s)
      2'b00: return a0;
      2'b01: return a1;
      2'b10: return a2;
      default: return a3;
    endcase
  endfunction
  let nibble_rev = {in[0], in[1], in[2], in[3]};

  // Internal consistency (implementation structure)
  property p_mux_impl;
    disable iff ($isunknown({sel,in0,in1,in2,in3}))
    selected_input == mux4(sel,in0,in1,in2,in3);
  endproperty
  assert property (@(*) p_mux_impl);

  property p_and_impl;
    disable iff ($isunknown({reversed_in,selected_input}))
    and_output == (reversed_in[7:4] & selected_input);
  endproperty
  assert property (@(*) p_and_impl);

  property p_out_impl;
    disable iff ($isunknown(and_output))
    out == and_output;
  endproperty
  assert property (@(*) p_out_impl);

  // Spec-intent checks (catch design/spec mismatch)
  property p_reverse_intent;
    disable iff ($isunknown(in))
    reversed_in == {in[0],in[1],in[2],in[3],in[4],in[5],in[6],in[7]};
  endproperty
  assert property (@(*) p_reverse_intent);

  property p_top_intent;
    disable iff ($isunknown({in,sel,in0,in1,in2,in3}))
    out == (mux4(sel,in0,in1,in2,in3) & nibble_rev);
  endproperty
  assert property (@(*) p_top_intent);

  // Port-level functional check of current implementation behavior
  // (keeps a direct port relation regardless of internal nets)
  property p_top_impl_ports;
    disable iff ($isunknown({in,sel,in0,in1,in2,in3}))
    out == (mux4(sel,in0,in1,in2,in3) & in[7:4]);
  endproperty
  assert property (@(*) p_top_impl_ports);

  // Basic X-check on output
  assert property (@(*) !$isunknown(out));

  // Coverage
  cover property (@(*) sel == 2'b00);
  cover property (@(*) sel == 2'b01);
  cover property (@(*) sel == 2'b10);
  cover property (@(*) sel == 2'b11);

  cover property (@(*) selected_input == 4'h0);
  cover property (@(*) selected_input == 4'hF);
  cover property (@(*) out == 4'h0);
  cover property (@(*) out == 4'hF);

  cover property (@(*) $changed(out));

endmodule

// Bind to the DUT (connects to ports and internal wires by name)
bind reverse_mux_and reverse_mux_and_sva i_reverse_mux_and_sva (.*);