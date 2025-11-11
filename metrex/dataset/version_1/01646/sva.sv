// SVA: binders
bind top_module top_module_sva();
bind adder4    adder4_sva();

// SVA for adder4
module adder4_sva;
  // Combinational correctness
  always_comb begin
    assert (sum == (a + b)) else $error("adder4: sum != a+b");
    assert (cout == sum[4]) else $error("adder4: cout != sum[4]");
    assert (cout == ((a + b) > 4'd15)) else $error("adder4: cout != carry(a+b)");
    // Coverage
    cover (a==4'd0  && b==4'd0);
    cover (a==4'd15 && b==4'd15);
    cover (cout==1'b0);
    cover (cout==1'b1);
  end
endmodule

// SVA for top_module
module top_module_sva;

  // Expected mux function (match DUT sizing/truncation/zero-extend)
  function automatic [4:0] exp_mux();
    automatic logic [4:0] s0  = (a0 + b0);
    automatic logic [4:0] s1  = (a1 + b1);
    automatic logic [5:0] add = s0 + s1;
    automatic logic [5:0] s01 = s0 - s1;
    automatic logic [5:0] s10 = s1 - s0;
    automatic logic [1:0] csum = cout0 + cout1;
    case (sel)
      3'd0: exp_mux = s0;
      3'd1: exp_mux = s1;
      3'd2: exp_mux = add[4:0];
      3'd3: exp_mux = s01[4:0];
      3'd4: exp_mux = s10[4:0];
      3'd5: exp_mux = {3'b000, csum};
      3'd6: exp_mux = {3'b000, and_out};
      default: exp_mux = {1'b0, 4'b1111};
    endcase
  endfunction

  always_comb begin
    // Local wiring/leaf checks
    assert (sum0  == (a0 + b0)) else $error("top: sum0 != a0+b0");
    assert (sum1  == (a1 + b1)) else $error("top: sum1 != a1+b1");
    assert (cout0 == sum0[4])   else $error("top: cout0 != sum0[4]");
    assert (cout1 == sum1[4])   else $error("top: cout1 != sum1[4]");
    assert (and_out == (a0[1:0] & b0[1:0] & a1[1:0] & b1[1:0]))
      else $error("top: and_out mismatch");

    // Mux output and final result
    assert (mux_out == exp_mux())         else $error("top: mux_out mismatch");
    assert (result  == mux_out[3:0])      else $error("top: result != mux_out[3:0]");

    // Explicit width/zero-extend checks for narrow arms
    if (sel == 3'd5) begin
      assert (mux_out[4:2] == 3'b000)                  else $error("top: sel=5 upper bits not zero");
      assert (mux_out[1:0] == (cout0 + cout1))         else $error("top: sel=5 LSBs != cout0+cout1");
    end
    if (sel == 3'd6) begin
      assert (mux_out[4:2] == 3'b000)                  else $error("top: sel=6 upper bits not zero");
      assert (mux_out[1:0] == and_out)                 else $error("top: sel=6 LSBs != and_out");
    end

    // Coverage: select lines
    cover (sel == 3'd0);
    cover (sel == 3'd1);
    cover (sel == 3'd2);
    cover (sel == 3'd3);
    cover (sel == 3'd4);
    cover (sel == 3'd5);
    cover (sel == 3'd6);
    cover (sel == 3'd7); // default arm

    // Coverage: arithmetic corner cases
    cover (sel == 3'd2 && (((a0+b0) + (a1+b1))[5] == 1'b1)); // overflow on add
    cover (sel == 3'd3 && ((a0+b0) < (a1+b1)));              // borrow s0 - s1
    cover (sel == 3'd4 && ((a1+b1) < (a0+b0)));              // borrow s1 - s0

    // Coverage: carry and AND cases
    cover (sel == 3'd5 && (cout0 + cout1) == 2);
    cover (sel == 3'd5 && (cout0 + cout1) == 1);
    cover (sel == 3'd6 && and_out == 2'b00);
    cover (sel == 3'd6 && and_out == 2'b11);
  end
endmodule