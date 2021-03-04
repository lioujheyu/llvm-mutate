#!/usr/bin/env python3
import argparse
import sys
import subprocess
import inspect
import os

try:
    import gevo._llvm
    from gevo import __version__
    from gevo._llvm import __llvm_version__

    LLVM_MUTATE_LIBRARY_PATH=f'{os.path.dirname(inspect.getfile(gevo._llvm))}/Mutate.so.{__llvm_version__}'
except ImportError:
    # TODO: load mutation.so from Mutate folder with proper llvm version string as a standalone mode
    print('Cannot find Mutate.so because gevo is not installed! ')
    sys.exit(-1)

class FileOpener(argparse.FileType):
    # delayed FileType;
    # sample use:
    # with args.input.open() as f: f.read()
    def __call__(self, string):
        # optionally test string
        self.filename = string
        return self
    def open(self):
        return super(FileOpener,self).__call__(self.filename)
    file =  property(open, None, None, 'open file property')

if __name__ == '__main__':
    # Command parser
    class MutationAction(argparse.Action):
        def __call__(self, parser, namespace, values, option_string=None):
            if 'mutation_commands' not in namespace:
                setattr(namespace, 'mutation_commands', [])
            previous_act = namespace.mutation_commands
            previous_act.append((self.dest, values))
            setattr(namespace, 'mutation_commands', previous_act)

    llvm_mutate_parser = argparse.ArgumentParser(description="Manipulate LLVM assembly from Nvidia CUDA Kernels")
    llvm_mutate_parser.add_argument('-o', '--output_file', metavar='FILE', type=FileOpener('w'), default='-',
        help='output file name. Output will be redirected to stdout if output file is not specified')
    llvm_mutate_parser.add_argument('-f', '--input_file', metavar='FILE', type=FileOpener('r'), default='-',
        help='input file name. llvm-mutate will use and wait for stdin as the input stream if input file is not specified.')
    llvm_mutate_parser.add_argument('-n', '--name', action='store_true',
        help='add unique ID (UID) for each instruction. UID is one of needed instruction description in mutation operations')
    llvm_mutate_parser.add_argument('-I', '--ids', action='store_true',
        help='show the number of instructions')
    llvm_mutate_parser.add_argument('-q', '--query', type=str, metavar='INST',
        help='query the instruction\'s source line info')
    llvm_mutate_parser.add_argument('--not_use_result', action='store_true',
        help='not connect the newly inserted instruction\'s result value back into the use-def\
              chain when performing mutation operations. This argument is mainly for reproducing\
              program variant from a sequence of mutations')
    llvm_mutate_parser.add_argument('-V', '--version', action='version', version='%(prog)s under gevo-' + __version__)

    # grouping mutation commands
    mutation_operation_group = llvm_mutate_parser.add_argument_group(
        title='Mutation Operations',
        description='Mutation operations only accept instruction description [INST] in 2 formats: \
                     integer number as instruction index or Unique ID. The advantage of UID is,  \
                     once created, persistence throughout the mutation operation as long as the \
                     the instruction UID denoted is not the target of mutation operation. \
                     Note: --name, --ids, and mutation operation cannot be used together.')
    mutation_operation_group.add_argument(
        '-c', '--cut', type=str, dest='-cut', action=MutationAction, metavar='INST',
        help='cut the given instruction')
    mutation_operation_group.add_argument(
        '-i', '--insert', type=str, dest='-insert', action=MutationAction, metavar='INST1,INST2',
        help='copy the second inst. before the first')
    mutation_operation_group.add_argument(
        '-p', '--oprepl', type=str, dest='-oprepl', action=MutationAction, metavar='INST1,INST2',
        help='replace the first Operand. with the second')
    mutation_operation_group.add_argument(
        '-r', '--replace', type=str, dest='-replace', action=MutationAction, metavar='INST1,INST2', 
        help='replace the first inst. with the second')
    mutation_operation_group.add_argument(
        '-m', '--move', type=str, dest='-move', action=MutationAction, metavar='INST1,INST2',
        help='move the second inst. before the first')
    mutation_operation_group.add_argument(
        '-s', '--swap', type=str, dest='-swap', action=MutationAction, metavar='INST1,INST2',
        help='swap the location of two instructions')

    args = llvm_mutate_parser.parse_args()
    OPT_NOT_USE_RESULT = '-use_result=0' if args.not_use_result else ''

    if args.name and 'mutation_commands' in args:
        print("--name and mutation operations cannot be used together.")
        sys.exit(-1)

    if args.name:
        opt_proc = subprocess.Popen(
            [ f'opt-{__llvm_version__}',
              '-load', LLVM_MUTATE_LIBRARY_PATH,
              '-name'],
            stdin=args.input_file.open(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE )
        opt_stdout, opt_stderr = opt_proc.communicate()
        if opt_proc.returncode != 0:
            print(f"llvm-mutate: Error in {opt_proc.args}")
            print(opt_stderr.decode(), end='')
            sys.exit(-1)
    elif args.ids:
        opt_proc = subprocess.Popen(
            [ f'opt-{__llvm_version__}',
              '-load', LLVM_MUTATE_LIBRARY_PATH,
              '-ids'],
            stdin=args.input_file.open(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE )
        opt_stdout, opt_stderr = opt_proc.communicate()
        if opt_proc.returncode != 0:
            print(f"llvm-mutate: Error in {opt_proc.args}")
            print(opt_stderr.decode(), end='')
            sys.exit(-1)
        print(opt_stderr.decode(), end='', file=sys.stderr)
        sys.exit(0)
    elif args.query:
        opt_proc = subprocess.Popen(
            [ f'opt-{__llvm_version__}',
              '-load', LLVM_MUTATE_LIBRARY_PATH,
              '-query', f'-inst1={args.query}'],
            stdin=args.input_file.open(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE )
        opt_stdout, opt_stderr = opt_proc.communicate()
        if opt_proc.returncode != 0:
            print(f"llvm-mutate: Error in {opt_proc.args}")
            print(opt_stderr.decode(), end='')
            sys.exit(-1)
        print(opt_stderr.decode(), end='', file=sys.stdout)
        sys.exit(0)
    elif 'mutation_commands' in args:
        with args.input_file.open() as f:
            input_str = f.buffer.read()
        for mop in args.mutation_commands:
            insts = mop[1].split(',')
            inst_args = [ f'-inst1={insts[0]}' ] if len(insts) == 1 else\
                        [ f'-inst1={insts[0]}', f'-inst2={insts[1]}']
            opt_args = [f'opt-{__llvm_version__}',
                        '-load', LLVM_MUTATE_LIBRARY_PATH,
                        '-use_result=0', mop[0]] if args.not_use_result else\
                       [f'opt-{__llvm_version__}',
                        '-load', LLVM_MUTATE_LIBRARY_PATH, mop[0]]

            opt_args.extend(inst_args)

            opt_proc = subprocess.Popen(
                opt_args,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE )
            opt_stdout, opt_stderr = opt_proc.communicate(input=input_str)

            if opt_proc.returncode != 0:
                print(f"llvm-mutate: opt error in {mop[0]} {mop[1]}")
                print(opt_stderr.decode(), end='')
                sys.exit(-1)

            # TODO: Have proper return code from Mutate.so. irind.py in gevo need to be changed as well
            print(opt_stderr.decode(), end='', file=sys.stderr)
            if opt_stderr.decode().find('failed') != -1:
                sys.exit(0)
            if opt_stderr.decode().find('mismatch') != -1:
                sys.exit(0)
            if opt_stderr.decode().find('no use') != -1:
                sys.exit(0)
            input_str = opt_stdout
    else:
        llvm_mutate_parser.print_help()
        sys.exit(-1)

    llvmdis_proc = subprocess.Popen(
        [ f'llvm-dis-{__llvm_version__}'],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE )
    llvmdis_stdout, llvmdis_stderr = llvmdis_proc.communicate(input=opt_stdout)
    if llvmdis_proc.returncode != 0:
        print(f"llvm-mutate: llc error in \"{' '.join(opt_proc.args)} | {' '.join(llvmdis_proc.args)}\"")
        print(llvmdis_stderr.decode())
        sys.exit(-1)

    print(llvmdis_stdout.decode(), file=args.output_file.open(), end='')

    # Link to PTX
    # cuda.init()
    # SM_MAJOR, SM_MINOR = cuda.Device(0).compute_capability()
    # MGPU = 'sm_' + str(SM_MAJOR) + str(SM_MINOR)

    # llc_proc = subprocess.Popen(
    #     [ f'llc{LLVM_VERSION}', "-march=nvptx64", "-mcpu="+MGPU, "-mattr=+ptx70"],
    #     # [ f'llc{LLVM_VERSION}'],
    #     stdin=subprocess.PIPE,
    #     stdout=subprocess.PIPE,
    #     stderr=subprocess.PIPE )
    # llc_stdout, llc_stderr = llc_proc.communicate(input=opt_stdout)
    # if llc_proc.returncode != 0:
    #     print(f"llvm-mutate: llc error in \"{' '.join(opt_proc.args)} | {' '.join(llc_proc.args)}\"")
    #     print(llc_stderr.decode())
    #     sys.exit(-1)
