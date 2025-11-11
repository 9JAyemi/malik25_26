// SVA for jt51_lin2exp
// Bind this module to the DUT instance or to the module type.
module jt51_lin2exp_sva(
  input logic [15:0] lin,
  input logic [9:0]  man,
  input logic [2:0]  exp
);

  // Reference model in functions (combinational, x-tolerant on lin[15:9])
  function automatic [2:0] exp_ref(input logic [15:0] l);
    logic [6:0] top;
    exp_ref = 3'd1;
    top = l[15:9];
    // find first transition from MSB downward among top[6:0]
    for (int i = 5; i >= 0; i--) begin
      if (!$isunknown({top[i+1], top[i]}) && (top[i+1] != top[i])) begin
        exp_ref = i + 3'd2; // i=5->7, ..., i=0->2
        break;
      end
    end
  endfunction

  function automatic [9:0] man_ref(input logic [15:0] l);
    case (exp_ref(l))
      3'd7: man_ref = l[15:6];
      3'd6: man_ref = l[14:5];
      3'd5: man_ref = l[13:4];
      3'd4: man_ref = l[12:3];
      3'd3: man_ref = l[11:2];
      3'd2: man_ref = l[10:1];
      default: man_ref = l[9:0]; // exp==1
    endcase
  endfunction

  // Sanity/range
  assert property ( !$isunknown(lin[15:9]) |-> (exp inside {[3'd1:3'd7]}) )
    else $error("jt51_lin2exp: exp out of range");

  assert property ( !$isunknown(lin[15:9]) |-> !$isunknown({man,exp}) )
    else $error("jt51_lin2exp: outputs contain X/Z for known lin[15:9]");

  // Functional equivalence (golden check)
  assert property ( !$isunknown(lin[15:9]) |-> ({man,exp} == {man_ref(lin),exp_ref(lin)}) )
    else $error("jt51_lin2exp: {man,exp} mismatch");

  // Optional direct slice consistency by exp (helps debug quickly)
  assert property ( exp==3'd7 |-> man==lin[15:6] );
  assert property ( exp==3'd6 |-> man==lin[14:5] );
  assert property ( exp==3'd5 |-> man==lin[13:4] );
  assert property ( exp==3'd4 |-> man==lin[12:3] );
  assert property ( exp==3'd3 |-> man==lin[11:2] );
  assert property ( exp==3'd2 |-> man==lin[10:1] );
  assert property ( exp==3'd1 |-> man==lin[9:0]  );

  // Branch/functional coverage (matches DUT casex items)
  // exp=7
  cover property ( lin[15:14]==2'b10 && exp==3'd7 );
  cover property ( lin[15:14]==2'b01 && exp==3'd7 );
  // exp=6
  cover property ( lin[15:13]==3'b110 && exp==3'd6 );
  cover property ( lin[15:13]==3'b001 && exp==3'd6 );
  // exp=5
  cover property ( lin[15:12]==4'b1110 && exp==3'd5 );
  cover property ( lin[15:12]==4'b0001 && exp==3'd5 );
  // exp=4
  cover property ( lin[15:11]==5'b11110 && exp==3'd4 );
  cover property ( lin[15:11]==5'b00001 && exp==3'd4 );
  // exp=3
  cover property ( lin[15:10]==6'b111110 && exp==3'd3 );
  cover property ( lin[15:10]==6'b000001 && exp==3'd3 );
  // exp=2
  cover property ( lin[15:9]==7'b1111110 && exp==3'd2 );
  cover property ( lin[15:9]==7'b0000001 && exp==3'd2 );
  // exp=1 (both saturating ends)
  cover property ( lin[15:9]==7'b1111111 && exp==3'd1 );
  cover property ( lin[15:9]==7'b0000000 && exp==3'd1 );

endmodule

// Bind to all instances of jt51_lin2exp
bind jt51_lin2exp jt51_lin2exp_sva sva_jt51_lin2exp(.*);