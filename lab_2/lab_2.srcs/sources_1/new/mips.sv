`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/12/2020 03:06:56 PM
// Design Name: 
// Module Name: mips
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

//ALU
//000 F = A & B
//001 F = A | B
//010 F = A + B
//100 F = A & (~B)
//101 F = A | (~B)
//110 F = A - B
//111 F = A < B
module alu(input  logic [31:0] alu_a,alu_b,
    input   logic [2:0]   alu_control,
    output  logic [31:0] alu_y,
    output  logic         zero
    );
    
    always_comb begin
        case(alu_control)
            3'b000:      alu_y = alu_a & alu_b;
            3'b001:       alu_y = alu_a | alu_b;
            3'b010:     alu_y = alu_a + alu_b;
            3'b100:  alu_y = alu_a &~alu_b;
            3'b101: alu_y = (alu_a - alu_b == 0 )? 1 : 0;
            3'b110:    alu_y = alu_a - alu_b;
            3'b111:      alu_y = alu_a < alu_b;
            3'b011:   alu_y = 0;
        endcase
    end
    assign zero = alu_y == 0 ? 1 : 0;
endmodule

//2-way multiplexer
//y = s ? d0 : d1
module mux2 #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] dO, dl,
    input logic s,
    output logic [WIDTH-1:0] y);
    
    assign y = s ? dl : dO;
endmodule

//register
//on the posedge of clk
//q <= d
//output q
//reset q to when reset is set as true
module flopr #(parameter WIDTH = 8)(
    input logic clk, reset,
    input logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q);
    
    always_ff @(posedge clk, posedge reset) begin
        if (reset) q <= 0;
        else q <= d;
    end
endmodule

//signed extension
// y = (int_32) a
module signext(
    input logic [15:0] a,
    output logic [31:0] y);
    
    assign y = {{16{a[15]}}, a};
endmodule

//shift left by 2
//y = a << 2
module sl2(
    input logic [31:0] a,
    output logic [31:0] y);
// shift left by 2
    assign y = {a[29:0], 2'b00};
endmodule

//adder
//y = a + b
module adder(
    input logic [31:0] a, b,
    output logic [31:0] y);
    assign y = a+b;
endmodule

//register file
//32 32-bit registers
//two read ports ra1, ra2
//one write port wa3
//write to register if we3 set as true
module regfile(
    input logic clk,
    input logic we3,
    input logic [4:0] ra1,ra2,wa3,
    input logic [31:0] wd3,
    output logic [31:0] rd1, rd2,
    output logic [31:0] regs [31:0]//added to shoot troubles
    );

    logic [31:0] rf[31:0];
// three ported register file
// read two ports combi nationally
// write third port on rising edge of clk
// register 0 hardwired to 0
// note: for pipelined processor, write third port
// on falling edge of clk
    assign regs = rf;
    always_ff @(posedge clk) begin
        if (we3) rf[wa3] <=wd3;
        assign rd1 = (ra1!=0) ? rf[ra1] : 0;
        assign rd2 = (ra2!=0) ? rf[ra2] : 0;
        //$display("wa3:%H, wd3:%H, ra1:%H, rd1:%H, ra2:%H, rd:%H", wa3, wd3, ra1, rf[ra1], ra2, rf[ra2]);
    end
endmodule

module datapath(
    input logic clk, reset,
    input logic memtoreg, pcsrc,
    input logic alusrc, regdst,
    input logic regwrite, jump,
    input logic [2:0] alucontrol,
    output logic zero,
    output logic [31:0] pc,
    input logic [31:0] instr,
    output logic [31:0] aluout, writedata,
    input logic [31:0] readdata,
    output logic [31:0] regs [31:0]
    );
    
    logic [4:0] writereg;
    logic [31:0] pcnext, pcnextbr, pcplus4, pcbranch;
    logic [31:0] signimm, signimmsh;
    logic [31:0] srca, srcb;
    logic [31:0] result;
    
    // next PC 1ogic
    //PC
    //instruction address, converted to @instr
    flopr#(32) pcreg(clk, reset, pcnext, pc);
    //@pcsrc and @jump decide next pc: next instruction, branching, ?
    //adder
    adder pcaddl(pc, 32'b100, pcplus4);
    //left shift by 2 bits
    sl2 immsh(signimm, signimmsh) ;
    //adder
    adder pcadd2(pcplus4, signimmsh, pcbranch);
    //2-way multiplexer
    mux2#(32) pcbrmux(pcplus4, pcbranch, pcsrc, pcnextbr);
    //2-way multiplexer
    mux2#(32) pcmux(pcnextbr, {pcplus4[31:28], instr[25:0], 2'b00}, jump, pcnext);
    
    // register file logic
    //register files
    regfile rf(clk, regwrite, instr[25:21], instr[20:16], writereg, result, srca, writedata, regs);
    
    //2-way multiplexer
    mux2#(5) wrmux(instr[20:16], instr[15:11], regdst, writereg);
    //2-way multiplexer
    mux2#(32) resmux(aluout, readdata, memtoreg, result);
    //signed extension
    signext se(instr[15:0], signimm);

    // ALU 1ogic
    //2-way multiplexer
    mux2#(32) srcbmux(writedata, signimm, alusrc, srcb);
    //alu
    alu alu(srca, srcb, alucontrol, aluout, zero);
    
    always_ff @(posedge clk) begin
        $display("pc:%H, instr:%H, op:%H, func:%H", pc, instr, instr[31:26], instr[5:0]);
        $display("srca:%H, srcb:%H, alucontrol:%H, aluout:%H, zero:%H",srca, srcb, alucontrol, aluout, zero);
    end
    
endmodule

//decide the alu control bit given the funct field and aluop field of the instruction
//combinational logic
module aludec(
    input logic [5:0] funct,
    input logic [1:0] aluop,
    output logic [2:0] alucontrol);
    
    always_comb
        case(aluop)
            2'b00: alucontrol <= 3'b010; // add (for lw/sw/addi) end;
            2'b01: alucontrol <= 3'b110; // sub (for beq) architecture behave of aludec is
            2'b11: alucontrol <= 3'b001;
            default: case(funct) // R-type instructions begin
                6'b100000: alucontrol <= 3'b010; // add process(al1 ) begin
                6'b100010: alucontrol <= 3'b110; // sub case aluop is
                6'b100100: alucontrol <= 3'b000; // and when "00" => alucontrol <= "010" ; -- add (for lw/sw/addi )
                6'b100101: alucontrol <= 3'b001; //or when "01" => alucontrol <= "110"; -- sub (for beq)
                6'b101010: alucontrol <= 3'b111; // sit when others => case funct is - R-type instructions
                default: alucontrol <= 3'bxxx; // ??? when "100000" => alucontrol <= "010"; - add
            endcase // when "100010" => alucontrol <= "110"; - sub
        endcase // when "100100" => alucontrol <= "000"; -- and
endmodule

//decide controls according to the opcode of instruction
//combinational logic
module maindec(
    input logic [5:0] op,
    output logic memtoreg, memwrite,//
    output logic branch, bne, alusrc,
    output logic regdst, regwrite,
    output logic jump,
    output logic [1:0] aluop
    );
    
    logic [9:0] controls;

    assign {regwrite, regdst, alusrc, branch, bne, memwrite, memtoreg, jump, aluop} = controls;

    always_comb
        case(op)
            6'b000000: controls <= 10'b1100000010; // RTYPE
            6'b100011: controls <= 10'b1010001000; // LW
            6'b101011: controls <= 10'b0010010000; // SW
            6'b000100: controls <= 10'b0001000001; // BEQ
            6'b000101: controls <= 10'b0001100001; // BNE
            6'b001000: controls <= 10'b1010000000; // ADDI
            6'b001101: controls <= 10'b1010000011; // ORI
            6'b000010: controls <= 10'b0000000100; // J
            default: controls <= 10'bxxxxxxxxxx; // illegal op
        endcase
endmodule

//combinational logic
//parse the instruction and decide the params of the datapath
module controller(
    input logic [5:0] op, funct,
    input logic zero,
    output logic memtoreg, memwrite,
    output logic pcsrc, alusrc,
    output logic regdst, regwrite,
    output logic jump,
    output logic [2:0] alucontrol);
    
    logic [1:0] aluop;
    logic branch;
    logic bne;
    
    maindec md(op, memtoreg, memwrite, branch, bne, alusrc, regdst, regwrite, jump, aluop);
    aludec ad(funct, aluop, alucontrol );

    assign pcsrc = branch & (bne^zero);
    
endmodule

//r: op(6) rs(5) rt(5) rd(5) shamt(5) funct(6)
//i: op(6) rs(5) rt(5) imm(16)
//j: op(6) addr(26)

//@pc -> @instr
//
//32bit MIPS cpu
//the core part of the project
module mips(
    input logic clk, reset,
    output logic [31:0] pc,
    input logic [31:0] instr,
    output logic memwrite,
    output logic [31:0] aluout, writedata,
    input logic [31:0] readdata,
    output logic [31:0] regs [31:0]);
    
    logic memtoreg, alusrc, regdst, regwrite, jump, pesre, zero;
    logic [2:0] alucontrol;

    controller c(instr[31:26], instr[5:0], zero, memtoreg, memwrite, pesre, alusrc, regdst, regwrite, jump, alucontrol);
    datapath dp(clk, reset, memtoreg, pesre, alusrc, regdst, regwrite, jump, alucontrol, zero, pc, instr, aluout, writedata, readdata, regs);

    
    always_ff@(posedge clk) begin
        $display("op:%H, jump:%b, alucontrol:%b", instr[31:26], jump, alucontrol);
    end

endmodule

//test
module testbench();

    logic clk;
    logic reset;
    
    logic [31:0] writedata, dataadr;
    logic memwrite;
    
    logic [31:0] regs [31:0];

    // instantiate device to be tested
    top dut(clk, reset, writedata, dataadr, memwrite, regs);

    // initialize test end component;
    // set PC as 0
    // start the CPU
    initial
        begin
            $display("Simulation started");
            reset <= 1; # 22; reset <= 0;
        end

    // time period = 10
    always
        begin
            clk <=1; # 5; clk <=0; #5;
        end


    // check results
    always @(negedge clk)
        begin
            if (memwrite)
                begin
                    if (dataadr === 84 & writedata === 7)
                        begin
                            $display("Simulation succeeded");
                            $stop;
                        end
                    else if (dataadr !== 80)
                        begin
                            $display("Simulation failed");
                            $stop;
                        end
                end
        end
endmodule

//the top module of the 32-bit MIPS machine
//clk is the clock signal that drives the whole state machine
//reset is used to reset the PC
//contains a 32-bit MIPS cpu, a data memory and an instruction memory
module top(
    input logic clk, reset,
    output logic [31:0] writedata, dataadr,
    output logic memwrite,
    output logic [31:0] regs [31:0]
    );
    
    logic [31:0] pc, instr, readdata;
    
    //instantiate processor and memories
    mips mips(clk, reset, pc, instr, memwrite, dataadr,writedata, readdata, regs);
    imem imem(pc[7:2], instr) ;
    dmem dmem(clk, memwrite, dataadr, writedata, readdata);
endmodule

//OK
//data memory 64*32 bits
//a sigle port, a is the address
//write to mem when we is set as true
module dmem(
    input logic clk, we,
    input logic [31:0] a, wd,
    output logic [31:0] rd
    );
    
    logic [31:0] RAM[63:0];
    
    assign rd = RAM[a[31:2]]; // word aligned
    
    always_ff @(posedge clk)
        if (we) RAM[a[31:2]] <= wd;
endmodule

//OK
//instruction memory 64*32 bit
//a single port
//initialized with memfile.dat
module imem(
    input logic [5:0] a,
    output logic [31:0] rd
    );
    
    logic [31:0] RAM[63:0];
    
    initial begin
        RAM[0] = 32'h20020004;
        RAM[1] = 32'h20030008;
        RAM[2] = 32'h34420001;//ori $2 1
        RAM[3] = 32'h34630004;//ori $3 4
        RAM[4] = 32'h2067fff7;
        RAM[5] = 32'h00e22025;
        RAM[6] = 32'h00642824;
        RAM[7] = 32'h00a42820;
        RAM[8] = 32'h10a7000a;
        RAM[9] = 32'h0064202a;
        RAM[10] = 32'h10800001;
        RAM[11] = 32'h20050000;
        RAM[12] = 32'h00e2202a;
        RAM[13] = 32'h00853820;
        RAM[14] = 32'h00e23822;
        RAM[15] = 32'hac670044;
        RAM[16] = 32'h8c020050;
        RAM[17] = 32'h14440001;//bne $2, $4, #end
        RAM[18] = 32'h20020001;
        RAM[19] = 32'hac020054;
        
        /*
        RAM[0] = 32'h20020005;
        RAM[1] = 32'h2003000c;
        RAM[0] = 32'h34020005;
        RAM[1] = 32'h3403000c;
        RAM[2] = 32'h2067fff7;
        RAM[3] = 32'h00e22025;
        RAM[4] = 32'h00642824;
        RAM[5] = 32'h00a42820;
        RAM[6] = 32'h10a7000a;
        RAM[7] = 32'h0064202a;
        RAM[8] = 32'h10800001;
        RAM[9] = 32'h20050000;
        RAM[10] = 32'h00e2202a;
        RAM[11] = 32'h00853820;
        RAM[12] = 32'h00e23822;
        RAM[13] = 32'hac670044;
        RAM[14] = 32'h8c020050;
        RAM[15] = 32'h08000011;
        RAM[16] = 32'h20020001;
        RAM[17] = 32'hac020054;
        */
        $display("%H %H %H %H", RAM[0], RAM[1], RAM[2], RAM[3]);
    end
    
    assign rd = RAM[a]; // word aligned
endmodule
